import SixTenCrossNormal

namespace QGI.SixTen.Cross

open Finset
open scoped BigOperators

private def active {n} (m : Nat) (i : Fin n) := m.testBit i.val

private def nearLeft (m : Nat) (j : R) : Nat :=
  (univ.filter fun x : L => active m x = true ∧ design x j = true).card

private def leftOK (i : L) (m : Nat) : Prop :=
  active m i = false ∧ ∀ j k : R, design i j = design i k → nearLeft m j = nearLeft m k

private def share (j w : R) := colGram design j w

private def coeff (m : Nat) (i : L) := (univ.filter fun w : R => design i w = true ∧ active m w = true).card
private def size (m : Nat) := (univ.filter fun w : R => active m w = true).card

private def eligible (k : Nat) (j : R) (m : Nat) : Prop :=
  (∀ w : R, active m w = true → share j w = k) ∧
  ∀ i x : L, design i j = design x j → coeff m i = coeff m x

private instance (j m) : Decidable (leftOK j m) := by unfold leftOK; infer_instance
private instance (k j m) : Decidable (eligible k j m) := by unfold eligible; infer_instance

private def halfA : Array Nat := #[392,304,104,100,290,76,44,265,50,81]
private def halfB : Array Nat := #[592,644,642,385,577,274,529,518,137,134]

private theorem leftChecked : ∀ i : L, ∀ m ∈ List.range 64, leftOK i m →
    (∀ h : L, active m h = false) ∨ (∀ h : L, active m h = decide (h ≠ i)) := by
  native_decide

private theorem rightChecked : ∀ k : Fin 2, ∀ j : R, ∀ m ∈ List.range 1024, eligible (k.val+1) j m →
    if size m = 0 then ∀ w : R, active m w = false
    else if size m = (if k.val=0 then 6 else 3) then ∀ w : R, active m w = decide (share j w = k.val+1)
    else m = halfA[j.val]! ∨ m = halfB[j.val]! := by
  native_decide

private def halfMask (pick : Nat) (j : R) := if pick.testBit j.val then halfB[j.val]! else halfA[j.val]!

private theorem noSymmetricHalf : ∀ pick ∈ List.range 1024, ¬∀ i j : R,
    active (halfMask pick i) j = active (halfMask pick j) i := by
  native_decide

private theorem intersections : ∀ i j : R, i ≠ j → share i j = 1 ∨ share i j = 2 := by native_decide
private theorem diagonalOnly : ∀ i j : R, share i j = share 0 0 ↔ i=j := by native_decide
private theorem diagonalValue : ∀ i : R, share i i = share 0 0 := by native_decide

theorem left_graph (A : L → L → Bool) (symm : ∀ i x, A i x = A x i) (diag : ∀ i, A i i = false)
    (law : ∀ (i : L) (j k : R), design i j = design i k →
      (univ.filter (fun x => A i x = true ∧ design x j = true)).card =
      (univ.filter (fun x => A i x = true ∧ design x k = true)).card) :
    ∀ i j x y, i ≠ j → x ≠ y → A i j = A x y := by
  have row (i : L) : (∀ h, A i h = false) ∨ (∀ h, A i h = decide (h ≠ i)) := by
    let m := encode (A i)
    have bits (h : L) : active m h = A i h := decode _ _
    have ok : leftOK i m := ⟨(bits i).trans (diag i),fun j k eq => by simpa only [nearLeft,bits] using law i j k eq⟩
    simpa only [bits] using leftChecked i m (List.mem_range.mpr (encode_lt _)) ok
  have constant (i j k : L) (hj : i ≠ j) (hk : i ≠ k) : A i j = A i k := by
    rcases row i with empty | full
    · rw [empty,empty]
    · rw [full,full]; simp [hj.symm,hk.symm]
  intro i j x y hij hxy
  by_cases same : i=x
  · subst x; exact constant i j y hij hxy
  · exact (constant i j x hij same).trans ((symm i x).trans (constant x i y (Ne.symm same) hxy))

def selectedDegree (A : R → R → Bool) (k : Nat) (j : R) : Nat :=
  (univ.filter fun w => A j w = true ∧ colGram design j w = k).card
def mixedDegree (A : R → R → Bool) (k : Nat) (i : L) (j : R) : Nat :=
  (univ.filter fun w => design i w = true ∧ (A j w = true ∧ colGram design j w = k)).card

/-- For the 6-by-10 design, any compatible symmetric adjacency on the
ten-point shore is determined by the intersection of its two columns.
At intersection one, the only proper nonempty local possibilities have three
neighbors. None of the 2^10 selections of those possibilities is symmetric. -/
theorem right_graph (A : R → R → Bool) (symm : ∀ i j, A i j = A j i)
    (diag : ∀ i, A i i = false) (regular : ∀ k j v, selectedDegree A k j = selectedDegree A k v)
    (mixed : ∀ k i h j, design i j = design h j → mixedDegree A k i j = mixedDegree A k h j) :
    ∀ j w h t, colGram design j w = colGram design h t → A j w = A h t := by
  classical
  have shareSymm : ∀ i j : R, share i j = share j i := by native_decide
  have level (k : Fin 2) : ∃ v : Bool, ∀ j w : R, share j w = k.val+1 → A j w = v := by
    let cell := fun j w : R => A j w && decide (share j w = k.val+1)
    let m := fun j : R => encode (cell j)
    have bits (j w : R) : active (m j) w = cell j w := decode _ _
    have ok (j : R) : eligible (k.val+1) j (m j) := by
      constructor
      · intro w hw; have test := (bits j w).symm.trans hw
        simp only [cell,Bool.and_eq_true,decide_eq_true_eq] at test
        exact test.2
      · intro i x eq; simpa only [coeff,bits,cell,Bool.and_eq_true,decide_eq_true_eq,share,mixedDegree]
          using mixed (k.val+1) i x j eq
    have degrees (j : R) : size (m j) = selectedDegree A (k.val+1) 0 := by
      simpa only [size,bits,cell,Bool.and_eq_true,decide_eq_true_eq,share,selectedDegree]
        using regular (k.val+1) j 0
    have check (j : R) := rightChecked k j (m j) (List.mem_range.mpr (encode_lt _)) (ok j)
    simp only [degrees] at check
    by_cases empty : selectedDegree A (k.val+1) 0 = 0
    · simp only [empty,if_true] at check
      exact ⟨false,fun j w eq => by simpa only [bits,cell,eq,decide_true,Bool.and_true] using check j w⟩
    · simp only [empty,if_false] at check
      by_cases full : selectedDegree A (k.val+1) 0 = (if k.val=0 then 6 else 3)
      · simp only [full,if_true] at check
        exact ⟨true,fun j w eq => by simpa only [bits,cell,eq,decide_true,Bool.and_true] using check j w⟩
      · simp only [full,if_false] at check
        let pick := encode (fun j : R => decide (m j = halfB[j.val]!))
        have select (j : R) : halfMask pick j = m j := by
          change (if (encode _).testBit j.val then _ else _) = _
          rw [decode]
          by_cases hb : m j = halfB[j.val]!
          · simp [hb]
          · have ha := (check j).resolve_right hb
            simpa only [hb,decide_false,Bool.false_eq_true,if_false] using ha.symm
        apply False.elim
        apply noSymmetricHalf pick (List.mem_range.mpr (encode_lt _))
        intro i j
        rw [select,select,bits,bits]
        simp only [cell,symm i j,shareSymm i j]
  intro i j x y he
  change share i j = share x y at he
  by_cases eq : i=j
  · subst j
    have equal := (diagonalOnly x y).mp (he.symm.trans (diagonalValue i))
    subst y; rw [diag,diag]
  · rcases intersections i j eq with one | two
    · obtain ⟨v,h⟩ := level 0
      exact (h _ _ one).trans (h _ _ (he.symm.trans one)).symm
    · obtain ⟨v,h⟩ := level 1
      exact (h _ _ two).trans (h _ _ (he.symm.trans two)).symm

end QGI.SixTen.Cross