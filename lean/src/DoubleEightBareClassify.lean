import DoubleEightBareEnum
import DoubleEightBareLaws
import data.DoubleEightBareWitnesses
import Mathlib.Data.List.Enum

namespace QGI.DoubleEight.BareClassify

open ShoreCensus (V)
open BareLaws
open BareWitnesses (Witness)

def matrix (rows : List Nat) : Bare :=
  fun i j => BareEnum.digit (rows.getD i.val 0) j.val

/-- Use the original low-bit-first anchor coordinates, so the column-zero
convention here is deliberately different from the normalized input masks. -/
def anchor (a : Fin 13) : Bare := fun i j =>
  ((BareWitnesses.anchors.getD a.val #[]).getD i.val 0).testBit j.val

def indices : Nat → List Nat
  | 2 => [0, 1, 2]
  | 3 => [3, 6]
  | 4 => [7, 8, 10]
  | _ => []

private def permPoint (p : Array Nat) (i : V) : V := Fin.ofNat' 8 (p.getD i.val 0)

private def Represents (d : Nat) (B : Bare) (w : Witness) : Prop :=
  w.anchor < 13 ∧ w.anchor ∈ indices d ∧
  (∀ i j, permPoint w.left i = permPoint w.left j → i = j) ∧
  (∀ i j, permPoint w.right i = permPoint w.right j → i = j) ∧
  ∀ i j, B i j = anchor (Fin.ofNat' 13 w.anchor) (permPoint w.left i) (permPoint w.right j)

private instance (d B w) : Decidable (Represents d B w) := by unfold Represents; infer_instance

/-- An excluded degree-two candidate supplies a histogram value and a row
whose frequency in the square of the Gram matrix differs from row zero.
For the other two degrees the witness identifies an orientation and one
occupied cell whose product value differs from the occupied (0,0) cell. -/
private def rejected (d : Nat) (B : Bare) (n : Nat) : Bool :=
  if d = 2 then
    let g := gram B
    decide (rowHistogram (mul g g) (n / 8) 0 ≠ rowHistogram (mul g g) (n / 8) (Fin.ofNat' 8 n))
  else
    let T := if n < 64 then B else BareLaws.flip B
    let i := Fin.ofNat' 8 (n / 8)
    let j := Fin.ofNat' 8 n
    let product := mul (level (gram T) 1) (bit T)
    decide (T 0 0 = true ∧ T i j = true ∧ product 0 0 ≠ product i j)

private theorem not_rejected {d B n} (h : Necessary B) : rejected d B n ≠ true := by
  unfold rejected
  split
  · exact fun bad => (of_decide_eq_true bad) (h.1.gram_square_rows _ _ _)
  · by_cases hl : n < 64
    · simp only [if_pos hl]
      intro bad
      obtain ⟨h₀, h₁, different⟩ := of_decide_eq_true bad
      exact different (h.1.supported _ _ _ _ h₀ h₁)
    · simp only [if_neg hl]
      intro bad
      obtain ⟨h₀, h₁, different⟩ := of_decide_eq_true bad
      exact different (h.2.supported _ _ _ _ h₀ h₁)

private def checkOne (d : Nat) (rows : List Nat) (code : Nat) : Bool :=
  if code < 128 then rejected d (matrix rows) code
  else decide (Represents d (matrix rows) (BareWitnesses.witnesses.getD (code - 128) default))

private def checkAll (d : Nat) : Bool :=
  let labels := BareWitnesses.codes d
  (BareEnum.candidates d).zipIdx.all fun (rows, i) => checkOne d rows (labels.getD i 0)

private theorem all_checked : checkAll 2 = true ∧ checkAll 3 = true ∧ checkAll 4 = true := by
  native_decide

/-- The three finite searches visit 13, 1,112 and 7,776 normalized matrices.
Their certificates give actual point permutations for three, four and three
surviving matrices. Several normalized versions can represent the same anchor. -/
theorem counts :
    (([2,3,4] : List Nat).map fun d => (BareEnum.candidates d).length) = [13,1112,7776] ∧
    (([2,3,4] : List Nat).map fun d => ((BareWitnesses.codes d).filter (· ≥ 128)).size) = [3,4,3]
    ∧ BareWitnesses.anchors.size = 13 ∧ (BareWitnesses.anchors.all (fun xs => xs.size == 8)) = true := by
  native_decide

attribute [local irreducible] BareEnum.candidates BareWitnesses.codes BareWitnesses.witnesses
  BareWitnesses.anchors matrix permPoint anchor

theorem classify {d : Nat} {rows : List Nat} (hd : d = 2 ∨ d = 3 ∨ d = 4)
    (member : rows ∈ BareEnum.candidates d) (h : Necessary (matrix rows)) :
    ∃ a : Fin 13, a.val ∈ indices d ∧ ∃ p q : V ≃ V,
      ∀ i j, matrix rows i j = anchor a (p i) (q j) := by
  have checked : checkAll d = true := by
    rcases hd with rfl | rfl | rfl
    · exact all_checked.1
    · exact all_checked.2.1
    · exact all_checked.2.2
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp member
  have each := List.forall_mem_zipIdx'.mp (List.all_eq_true.mp checked) i hi
  change checkOne d _ _ = true at each
  unfold checkOne at each
  split at each
  · exact False.elim (not_rejected h each)
  · obtain ⟨ha, hm, hp, hq, coordinates⟩ := of_decide_eq_true each
    exact ⟨⟨_, ha⟩, hm, Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hp),
      Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hq), by
        simpa only [Fin.ofNat', Nat.mod_eq_of_lt ha] using coordinates⟩

private def LayerCertificate (a : Fin 13) (m : BareWitnesses.LayerMap) : Prop :=
  m.stratum < 88 ∧
  (∀ i j, permPoint m.left i = permPoint m.left j → i = j) ∧
  (∀ i j, permPoint m.right i = permPoint m.right j → i = j) ∧
  (∀ i j, anchor a i j = true ↔
    FixedInterface.named (Nonuniform.layer (Fin.ofNat' 88 m.stratum)).word
      (permPoint m.left i) (permPoint m.right j) = m.occupiedColor) ∧
  ∀ i j x y : V,
    anchor a i j = anchor a x y ↔
    let word := (Nonuniform.layer (Fin.ofNat' 88 m.stratum)).word
    FixedInterface.named word (permPoint m.left i) (permPoint m.right j) =
      FixedInterface.named word (permPoint m.left x) (permPoint m.right y)

private instance (a m) : Decidable (LayerCertificate a m) := by unfold LayerCertificate; infer_instance

private theorem layer_checked : ∀ a : Fin 13,
    LayerCertificate a (BareWitnesses.toLayers.getD a.val default) := by native_decide

/-- Every original bare anchor, including the ones excluded above, gives
a two-color partition on a specific actual nonuniform layer. No exchange
of the shores is required; the two occupied/complement names can change. -/
theorem anchor_layer (a : Fin 13) :
    ∃ (k : Fin 88) (p q : V ≃ V), ∀ i j x y,
      anchor a i j = anchor a x y ↔
      FixedInterface.named (Nonuniform.layer k).word (p i) (q j) =
        FixedInterface.named (Nonuniform.layer k).word (p x) (q y) := by
  obtain ⟨_, hp, hq, _, cells⟩ := layer_checked a
  exact ⟨_, Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hp),
    Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hq), cells⟩

end QGI.DoubleEight.BareClassify
