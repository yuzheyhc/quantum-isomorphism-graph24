import DoubleEightShoreCheck
import DoubleEightLayerCheck
import DoubleEightDecorations
import data.DoubleEightUniformInput
import Mathlib.Data.List.Permutation

namespace QGI.DoubleEight.ShoreCheck

theorem bank_checked : checkBank UniformInput.shores = true := by native_decide

private theorem witnesses_checked : checkWitnesses UniformInput.shores = true := by native_decide

private theorem every_relabeling_checked :
    checkEveryRelabeling UniformInput.shores (List.range 8).permutations = true := by native_decide

/-- The 11,196 input words are exactly all point relabelings of the 21 supplied
shore representatives, normalized by the first occurrence of each color. -/
theorem bank_iff_relabeling {w : Word} :
    w ∈ bank ↔ ∃ s ∈ UniformInput.shores.toList, ∃ p : List Nat,
      p.Perm (List.range 8) ∧ relabel s p.toArray = w := by
  constructor
  · intro hw
    obtain ⟨p, hs, hp, equal⟩ := has_witness_of_check witnesses_checked hw
    refine ⟨UniformInput.shores[p.seed]!, ?_, p.permutation.toList, hp, ?_⟩
    · rw [getElem!_pos UniformInput.shores p.seed hs]
      exact Array.getElem_mem_toList hs
    · simpa only [Array.toArray_toList] using equal
  · rintro ⟨s, hs, p, hp, rfl⟩
    exact relabel_mem_of_check every_relabeling_checked hs (List.mem_permutations.mpr hp)

def labeledLayers : Array (Word × Nat × Nat) :=
  Layers.layers.map fun l => (l.word, l.left, l.right)

/-- Both one-shore counts for each of the 89 interfaces, recomputed from
incidence masks for all members of the complete supplied-seed relabeling bank. -/
theorem counts_checked : checkCounts labeledLayers = true := by native_decide

theorem placements_by_layer :
    counts (labeledLayers.map Prod.fst) = labeledLayers.map Prod.snd := by
  have ok := counts_checked
  simp only [checkCounts, Bool.and_eq_true, beq_iff_eq] at ok
  exact ok.2

theorem sum_placements :
    (counts (labeledLayers.map Prod.fst)).foldl (fun s pair => s + pair.1 * pair.2) 0 =
      125564305 := by
  rw [placements_by_layer]
  native_decide

def orientedInterfaces : List Word :=
  (Layers.layers.toList.map (·.word)) ++ (Layers.layers.toList.map fun l => transposeWord l.word)

private theorem all_excluded_checked : orientedInterfaces.all checkExcluded = true := by native_decide

/-- For every actual interface, in either orientation, intersection-regular
bank choices occur in the computed list. Each omitted word has an
individually verified counterexample consisting of two explicit matrix entries. -/
theorem selected_of_intersection_regular {w a : Word} (hw : w ∈ orientedInterfaces)
    (ha : a ∈ bank) (h : IntersectionRegular w a) : a ∈ (legalWords w).toList :=
  selected_of_excluded_check (List.all_eq_true.mp all_excluded_checked w hw) ha h

end QGI.DoubleEight.ShoreCheck
