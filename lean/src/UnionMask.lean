import HomogeneousUnions

namespace QGI.Homogeneous.Unions

private abbrev Samples (n : Nat) := Array (Option (Fin n × Fin n))

/-- Keep one pair of vertices for each bit in a single pass over the table. -/
private def samples (n : Nat) (code : UnionCode) : Samples n := Id.run do
  let mut cells : Samples n := Array.replicate (code.orbitCount + 1) none
  for i in List.finRange n do
    for j in List.finRange n do
      cells := cells.setIfInBounds (bitIndex code i.val j.val) (some (i, j))
  return cells

private def sampleAt {n : Nat} (s : Samples n) (k : Nat) : Option (Fin n × Fin n) :=
  (s[k]?).join

private def sameOrReverse {n : Nat} (t : Table) (i j : Fin n) :
    Option (Fin n × Fin n) → Prop
  | none => False
  | some (u, v) => colorAt t i j = colorAt t u v ∨ colorAt t i j = colorAt t v u

private instance {n : Nat} (t : Table) (i j : Fin n) (p : Option (Fin n × Fin n)) :
    Decidable (sameOrReverse t i j p) := by
  cases p <;> unfold sameOrReverse <;> infer_instance

private def cellOK {n : Nat} (t : Table) (code : UnionCode) (s : Samples n)
    (i j : Fin n) : Bool :=
  let k := bitIndex code i j
  if k = 0 then i == j
  else decide (k ≤ code.orbitCount) && decide (sameOrReverse t i j (sampleAt s k))

private def allCellsOK {n : Nat} (t : Table) (code : UnionCode) (s : Samples n) : Prop :=
  ∀ i j : Fin n, cellOK t code s i j = true

private instance {n : Nat} (t : Table) (code : UnionCode) (s : Samples n) :
    Decidable (allCellsOK t code s) := by unfold allCellsOK; infer_instance

/-- Bit zero occurs only on the diagonal. Each cell with a positive bit
has the same color as that bit's sample cell or its transpose. -/
def MaskCompatible (n : Nat) (t : Table) (code : UnionCode) : Prop :=
  allCellsOK t code (samples n code)

instance (n : Nat) (t : Table) (code : UnionCode) : Decidable (MaskCompatible n t code) :=
  inferInstanceAs (Decidable (allCellsOK t code (samples n code)))

private def maskOf {r : Nat} (f : Fin r → Bool) : Nat :=
  (BitVec.ofBoolListLE (List.ofFn f)).toNat

private theorem mask_bound {r : Nat} (f : Fin r → Bool) : maskOf f < 2 ^ r := by
  simpa only [List.length_ofFn] using (BitVec.ofBoolListLE (List.ofFn f)).isLt

private theorem mask_entry {r : Nat} (f : Fin r → Bool) (k : Fin r) :
    (maskOf f >>> k.val) &&& 1 = (f k).toNat := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, ← Nat.toNat_testBit]
  unfold maskOf
  rw [BitVec.testBit_toNat, BitVec.getLsb_ofBoolListLE]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using k.isLt)]
  simp

/-- Every symmetric, loopless union of the raw colors is represented by
a mask checked by the scheme-union verifier. -/
theorem exists_mask_of_compatible {n : Nat} {t : Table} {code : UnionCode}
    (ok : MaskCompatible n t code) (G : Fin n → Fin n → Bool)
    (hs : ∀ i j, G i j = G j i) (hl : ∀ i, G i i = false)
    (hc : ∀ i j u v : Fin n, colorAt t i j = colorAt t u v → G i j = G u v) :
    ∃ mask < 2 ^ code.orbitCount, ∀ i j : Fin n, edge code mask i j = (G i j).toNat := by
  let s := samples n code
  let f : Fin code.orbitCount → Bool := fun b =>
    match sampleAt s (b.val + 1) with
    | none => false
    | some (u, v) => G u v
  refine ⟨maskOf f, mask_bound f, ?_⟩
  intro i j
  let k := bitIndex code i j
  have hcell : cellOK t code s i j = true := ok i j
  change (if k = 0 then i == j else decide (k ≤ code.orbitCount) &&
    decide (sameOrReverse t i j (sampleAt s k))) = true at hcell
  by_cases h0 : k = 0
  · have he : i = j := by simpa only [if_pos h0, beq_iff_eq] using hcell
    change (if k = 0 then 0 else _) = (G i j).toNat
    rw [if_pos h0, he, hl]
    rfl
  · have hcell' : k ≤ code.orbitCount ∧ sameOrReverse t i j (sampleAt s k) := by
      simpa only [if_neg h0, Bool.and_eq_true, decide_eq_true_eq] using hcell
    let b : Fin code.orbitCount := ⟨k - 1, by obtain ⟨hb, _⟩ := hcell'; omega⟩
    have back : b.val + 1 = k := by change k - 1 + 1 = k; omega
    have selected : f b = G i j := by
      change (match sampleAt s (b.val + 1) with | none => false | some (u, v) => G u v) = _
      rw [back]
      cases hp : sampleAt s k with
      | none =>
        have impossible := hcell'.2
        rw [hp] at impossible
        exact False.elim impossible
      | some p =>
        obtain ⟨u, v⟩ := p
        have colors := hcell'.2
        rw [hp] at colors
        rcases colors with colors | colors
        · exact (hc i j u v colors).symm
        · exact (hs u v).trans (hc i j v u colors).symm
    change (if k = 0 then 0 else _) = (G i j).toNat
    rw [if_neg h0]
    exact (mask_entry f b).trans (congrArg Bool.toNat selected)

end QGI.Homogeneous.Unions
