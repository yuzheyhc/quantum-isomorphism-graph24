import DoubleEightPlacementCheck
import DoubleEightLayerCheck
import DoubleEightShoreCertificate

namespace QGI.DoubleEight.Nonuniform

open Placements

def witnesses : Array Witness :=
  let raw := (include_str "data/double-eight-nonuniform-witnesses.txt").trim
  ((raw.splitOn "\n").mapM parseWitness).getD [] |>.toArray

def layer (k : Fin 88) : Layers.Layer := Layers.layers[k.val + 1]!

def stratum (k : Fin 88) : Stratum :=
  let c := (layer k).word
  let start := (((Layers.layers.toList.drop 1).take k.val).map Layers.Layer.product).sum
  ⟨c, ShoreCheck.legalWords c, ShoreCheck.legalWords (ShoreCheck.transposeWord c), start⟩

set_option maxRecDepth 100000 in
private theorem verified : ∀ k : Fin 88, checkStratum Layers.matrices witnesses (stratum k) = true := by
  native_decide

theorem placement_count :
    witnesses.size = 213889 ∧
    ((Layers.layers.toList.drop 1).map Layers.Layer.product).sum = witnesses.size := by
  native_decide

/-- A point bijection preserves and reflects the complete partition of the
256 ordered pairs. This conclusion has no assumption about group orders. -/
def Realized (c l r m : Word) : Prop :=
  ∃ f : Vertex ≃ Vertex, ∀ i j x y : Vertex,
    model c l r i j = model c l r x y ↔ color m (f i) (f j) = color m (f x) (f y)

private theorem realizes_checked_pair {rows : Array Word} {ws : Array Witness} {s : Stratum}
    {i j : Nat} {l r : Word} (hl : s.left[i]? = some l) (hr : s.right[j]? = some r)
    (ok : checkPair rows ws s i j = true) : ∃ (t : Nat) (m : Word),
      rows[t]? = some m ∧ Realized s.cross l r m := by
  cases hw : ws[s.start + i * s.right.size + j]? with
  | none => simp [checkPair, hw] at ok
  | some w =>
    cases hm : rows[w.row]? with
    | none => simp [checkPair, hl, hr, hw, hm] at ok
    | some m =>
      have h : checkPlacement s.cross l r m w.points = true := by
        simpa only [checkPair, hl, hr, hw, hm] using ok
      obtain ⟨left, right, colors⟩ := sound h
      refine ⟨w.row, m, hm, Equiv.ofBijective (point w.points) ⟨?_, ?_⟩, colors⟩
      · exact Function.LeftInverse.injective left
      · exact Function.RightInverse.surjective right

/-- Every pair returned by the two compatibility filters for any of the 88
nonuniform interfaces has a point-realized full representative in the actual
636-row catalogue. The 73 empty layers are included in this statement. -/
theorem every_listed_placement (k : Fin 88) {l r : Word}
    (hl : l ∈ ShoreCheck.legalWords (layer k).word)
    (hr : r ∈ ShoreCheck.legalWords (ShoreCheck.transposeWord (layer k).word)) :
    ∃ (t : Nat) (m : Word), Layers.matrices[t]? = some m ∧ Realized (layer k).word l r m := by
  change l ∈ (stratum k).left at hl
  change r ∈ (stratum k).right at hr
  obtain ⟨i, hi, hi'⟩ := Array.getElem_of_mem hl
  obtain ⟨j, hj, hj'⟩ := Array.getElem_of_mem hr
  have pair := List.all_eq_true.mp (List.all_eq_true.mp (verified k) i
    (List.mem_range.mpr hi)) j (List.mem_range.mpr hj)
  exact realizes_checked_pair (by simpa only [Array.getElem?_eq_getElem hi] using congrArg some hi')
    (by simpa only [Array.getElem?_eq_getElem hj] using congrArg some hj') pair

end QGI.DoubleEight.Nonuniform
