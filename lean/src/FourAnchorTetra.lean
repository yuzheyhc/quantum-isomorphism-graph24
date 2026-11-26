import ColoredPlanarWitness
import StrategyColorLaws
import Mathlib.Data.Fin.VecNotation

noncomputable section

namespace QGI.Coherent.FourAnchorTetra
open Certificate StrategyColorLaws

abbrev V := Fin 16
abbrev Table := V → V → Nat

private def matrix (c : Table) : ColorMatrix :=
  ⟨16,0,Array.ofFn fun k : Fin 256 => c ⟨k.val / 16,by omega⟩ ⟨k.val % 16,by omega⟩⟩

private theorem entry (c : Table) (i j : V) : (matrix c).get i.val j.val = c i j := by
  have bound : i.val * 16 + j.val < 256 := by omega
  have a : (i.val*16+j.val)/16=i.val := by omega
  have b : (i.val*16+j.val)%16=j.val := by omega
  simp [ColorMatrix.get,matrix,bound,a,b]

private theorem choose_pos (f : Nat → Nat) :
    0 < ((List.range 16).map f).sum ↔ ∃ i : V, 0 < f i.val := by
  have pos (xs : List Nat) : 0 < (xs.map f).sum ↔ ∃ i ∈ xs, 0 < f i := by
    induction xs with
    | nil => simp
    | cons v vs ih =>
      simp only [List.map_cons,List.sum_cons,Nat.add_pos_iff_pos_or_pos,ih,List.mem_cons,
        exists_eq_or_imp]
  rw [pos]
  exact ⟨fun ⟨i,hi,found⟩ => ⟨⟨i,List.mem_range.mp hi⟩,found⟩,
    fun ⟨i,found⟩ => ⟨i.val,List.mem_range.mpr i.isLt,found⟩⟩

private def names (c : Table) (u : Fin 4 → V) : List Nat :=
  [c (u 0) (u 1),c (u 0) (u 2),c (u 0) (u 3),c (u 1) (u 2),c (u 1) (u 3),c (u 2) (u 3)]

private def sixEdges (c d : Table) (u : Fin 4 → V) (a b e f : V) : Prop :=
  d a b = c (u 0) (u 1) ∧ d a e = c (u 0) (u 2) ∧ d a f = c (u 0) (u 3) ∧
  d b e = c (u 1) (u 2) ∧ d b f = c (u 1) (u 3) ∧ d e f = c (u 2) (u 3)

private theorem positive_iff (c d : Table) (u : Fin 4 → V) :
    0 < binaryCspCount (matrix d) .tetra (names c u) ↔ ∃ a b e f, sixEdges c d u a b e f := by
  simp only [binaryCspCount,Pattern.order,assignmentSum,show (matrix d).order=16 from rfl,choose_pos]
  apply exists_congr; intro a
  apply exists_congr; intro b
  apply exists_congr; intro e
  apply exists_congr; intro f
  have positive (P : Prop) [Decidable P] : (0 < (if P then 1 else 0 : Nat)) ↔ P := by
    by_cases h : P <;> simp [h]
  simp [satisfies,Pattern.edges,paintedArcs,names,sixEdges,entry,positive]

/-- Any four source points admit four simultaneous target choices with
the specified six directed colors. This uses the planar tetrahedron. -/
theorem synchronize {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) (u : Fin 4 → V) :
    ∃ v : Fin 4 → V, ∀ i j, i < j →
      Relations.color (closure G) (u i) (u j) = targetName p (v i) (v j) := by
  let c := Relations.color (closure G)
  let d := targetName p
  let colors := names c u
  have indicator (c : Table) (s : Nat) : binaryMatrix (n := 16) (matrix c) s = mark c s := by
    apply Matrix.ext
    intro x y
    by_cases h : c x y = s <;> simp [binaryMatrix,binary,entry,mark,h]
  have transport := planar_homCount (by decide : 0 < 16) p (matrix c) (matrix d) rfl rfl
    .tetra (drawing_of_tetraPrism (by decide)) colors rfl id (fun s _ => by
      rw [indicator,indicator]; exact mark_intertwines p s)
  rw [homCount_eq_binaryCspCount,homCount_eq_binaryCspCount,List.map_id_fun] at transport
  have pos := (positive_iff c c u).mpr ⟨u 0,u 1,u 2,u 3,by simp [sixEdges]⟩
  rw [show names c u = colors from rfl,transport] at pos
  obtain ⟨a,b,e,f,six⟩ := (positive_iff c d u).mp pos
  refine ⟨![a,b,e,f],?_⟩
  intro i j hij
  change c (u i) (u j) = d _ _
  obtain ⟨h01,h02,h03,h12,h13,h23⟩ := six
  fin_cases i <;> fin_cases j <;> first
    | exact h01.symm
    | exact h02.symm
    | exact h03.symm
    | exact h12.symm
    | exact h13.symm
    | exact h23.symm
    | exfalso; norm_num [Fin.lt_def] at hij

end QGI.Coherent.FourAnchorTetra