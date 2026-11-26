import RegionalPlanar
import FourAnchorTetra
import FourTwelveFunctional

noncomputable section
namespace QGI.Coherent.LargeOrderTetra
open Certificate SmallShore StrategyColorLaws
open FourTwelveFunctional (source)

private def matrix {k : Nat} (c : Table k) : ColorMatrix :=
  ⟨k,0,Array.ofFn fun i : Fin (k*k) =>
    c (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2⟩

private theorem entry {k} (c : Table k) (i j : Fin k) : (matrix c).get i.val j.val=c i j := by
  let z := finProdFinEquiv (i,j)
  have idx : z.val=i.val*k+j.val := by simp [z,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  have lt : i.val*k+j.val<k*k := idx ▸ z.isLt
  have pair : finProdFinEquiv.symm (⟨i.val*k+j.val,lt⟩ : Fin (k*k))=(i,j) := by
    rw [show (⟨i.val*k+j.val,lt⟩ : Fin (k*k))=z from Fin.ext idx.symm]
    exact finProdFinEquiv.symm_apply_apply _
  simp only [ColorMatrix.get,matrix,Array.getElem?_ofFn,dif_pos lt,Option.getD_some,pair]

private theorem choose_pos {k : Nat} (f : Nat → Nat) :
    0 < ((List.range k).map f).sum ↔ ∃ i : Fin k, 0 < f i.val := by
  have pos (xs : List Nat) : 0 < (xs.map f).sum ↔ ∃ i ∈ xs, 0 < f i := by
    induction xs with
    | nil => simp
    | cons v vs ih =>
      simp only [List.map_cons,List.sum_cons,Nat.add_pos_iff_pos_or_pos,ih,List.mem_cons,
        exists_eq_or_imp]
  rw [pos]
  exact ⟨fun ⟨i,hi,found⟩ => ⟨⟨i,List.mem_range.mp hi⟩,found⟩,
    fun ⟨i,found⟩ => ⟨i.val,List.mem_range.mpr i.isLt,found⟩⟩

private def names {k : Nat} (c : Table k) (u : Fin 4 → Fin k) : List Nat :=
  [c (u 0) (u 1),c (u 0) (u 2),c (u 0) (u 3),c (u 1) (u 2),c (u 1) (u 3),c (u 2) (u 3)]

private def sixEdges {k : Nat} (c d : Table k) (u : Fin 4 → Fin k) (a b e f : Fin k) : Prop :=
  d a b = c (u 0) (u 1) ∧ d a e = c (u 0) (u 2) ∧ d a f = c (u 0) (u 3) ∧
  d b e = c (u 1) (u 2) ∧ d b f = c (u 1) (u 3) ∧ d e f = c (u 2) (u 3)

private theorem positive_iff {k : Nat} (c d : Table k) (u : Fin 4 → Fin k) :
    0 < binaryCspCount (matrix d) .tetra (names c u) ↔ ∃ a b e f, sixEdges c d u a b e f := by
  simp only [binaryCspCount,Pattern.order,assignmentSum,show (matrix d).order=k from rfl,choose_pos]
  apply exists_congr; intro a
  apply exists_congr; intro b
  apply exists_congr; intro e
  apply exists_congr; intro f
  have positive (P : Prop) [Decidable P] : (0 < (if P then 1 else 0 : Nat)) ↔ P := by
    by_cases h : P <;> simp [h]
  simp [satisfies,Pattern.edges,paintedArcs,names,sixEdges,entry,positive]

theorem tetra {n k} {G H : Graph n} {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (p : PerfectStrategy G H K)
    (region : Nat → Prop) (f g : Fin k → Fin n) (hf : Function.Injective f) (hg : Function.Injective g)
    (sf : ∀ z, (∃ i, f i=z) ↔ region (source G z z))
    (sg : ∀ z, (∃ i, g i=z) ↔ region (targetName p z z)) (u : Fin 4 → Fin k) :
    ∃ v : Fin 4 → Fin k, ∀ i j,
      source G (f (u i)) (f (u j)) = targetName p (g (v i)) (g (v j)) := by
  let c := SmallShore.restrict (source G) f
  let d := SmallShore.restrict (targetName p) g
  have tr := RegionalPlanar.homCount_region p (Nat.zero_lt_of_lt (u 0).isLt) region f g hf hg sf sg
    (matrix c) (matrix d) rfl rfl .tetra (drawing_of_tetraPrism (by decide))
    (names c u) rfl id (fun i j a b hit s _ => by
      rw [entry,entry]; exact congrArg (fun z => z=s) hit |> Iff.of_eq)
  rw [homCount_eq_binaryCspCount,homCount_eq_binaryCspCount,List.map_id_fun] at tr
  have pos := (positive_iff c c u).mpr ⟨u 0,u 1,u 2,u 3,by simp [sixEdges]⟩
  rw [tr] at pos
  obtain ⟨a,b,e,t,h01,h02,h03,h12,h13,h23⟩ := (positive_iff c d u).mp pos
  let v : Fin 4 → Fin k := ![a,b,e,t]
  have pair (i j : Fin 4) (lt : i < j) : c (u i) (u j) = d (v i) (v j) := by
    fin_cases i <;> fin_cases j <;> first
      | exact h01.symm | exact h02.symm | exact h03.symm
      | exact h12.symm | exact h13.symm | exact h23.symm
      | exfalso; norm_num [Fin.lt_def] at lt
  refine ⟨v,fun i j => ?_⟩
  rcases lt_trichotomy i j with lt | rfl | gt
  · exact pair i j lt
  · by_cases lt : i < 3
    · exact (SmallShore.endpoints p (pair i 3 lt)).1
    · exact (SmallShore.endpoints p (pair 0 i (by omega))).2
  · exact common_transpose p (pair j i gt)


theorem synchronize {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) (u : Fin 4 → Fin n) :
    ∃ v : Fin 4 → Fin n, ∀ i j, source G (u i) (u j)=targetName p (v i) (v j) :=
  tetra p (fun _ => True) id id Function.injective_id Function.injective_id
    (fun z => iff_of_true ⟨z,rfl⟩ trivial) (fun z => iff_of_true ⟨z,rfl⟩ trivial) u

end QGI.Coherent.LargeOrderTetra
