import ZivAvCoreCheck
import certificates.Witnesses

namespace QGI.ZivAv
open SixteenMapSearch Certificate

def badMaps : List (List Nat) := [
  [0,1,2,3,4,5,6,7,8,9,11,10],
  [0,1,2,3,4,5,6,8,7,9,10,11],
  [0,1,3,2,5,4,6,7,8,9,11,10],
  [0,1,3,2,5,4,6,8,7,9,10,11]]

def witnessColors := [7,5,4,3,10,10,4,5,10]

theorem checked {pi : List Nat} (h : pi ∈ badMaps) :
    check m_fourteen_249 m_fourteen_249 .nearClique pi witnessColors 24 0 = true := by
  simp only [badMaps,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact cert_fourteen_680
  · exact cert_fourteen_681
  · exact cert_fourteen_682
  · exact cert_fourteen_683

theorem original_matches : ∀ a : Index, (original a).1 = 249 →
    ∀ i j : Vertex, color a i j = m_fourteen_249.get i.val j.val := by native_decide

private def run (a : Index) : Bool :=
  (misses (keyed a)).all fun pi => (original a).1 == 249 && badMaps.contains pi

set_option maxRecDepth 100000 in
private theorem exhaust : ∀ a : Index, run a = true := by native_decide

theorem obstruction {a : Index} {pi : List Nat} (hm : pi ∈ enumeratedMaps (keyed a) (keyed a))
    (hn : pointCheck (keyed a) pi = false) :
    (original a).1 = 249 ∧ pi ∈ badMaps := by
  have fail : pi ∈ misses (keyed a) := List.mem_filter.mpr ⟨hm,by simp [hn]⟩
  simpa only [Bool.and_eq_true,beq_iff_eq,List.contains_iff_mem] using List.all_eq_true.mp (exhaust a) pi fail

end QGI.ZivAv
