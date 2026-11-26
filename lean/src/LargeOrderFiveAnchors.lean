import LargeOrderTetra
import SixTenCoordinates

noncomputable section
namespace QGI.Coherent.LargeOrderFiveAnchors
open Certificate SmallShore StrategyColorLaws
open FourTwelveFunctional (source)
open private matrix entry choose_pos from LargeOrderTetra

private def names {k} (c : Table k) (u : Fin 5 → Fin k) :=
  [c (u 0) (u 2),c (u 0) (u 3),c (u 0) (u 4),c (u 1) (u 2),c (u 1) (u 3),c (u 1) (u 4),
    c (u 2) (u 3),c (u 2) (u 4),c (u 3) (u 4)]
private def nine {k} (c d : Table k) (u : Fin 5 → Fin k) (a b e f g : Fin k) :=
  d a e=c (u 0) (u 2) ∧ d a f=c (u 0) (u 3) ∧ d a g=c (u 0) (u 4) ∧
  d b e=c (u 1) (u 2) ∧ d b f=c (u 1) (u 3) ∧ d b g=c (u 1) (u 4) ∧
  d e f=c (u 2) (u 3) ∧ d e g=c (u 2) (u 4) ∧ d f g=c (u 3) (u 4)
private theorem positive {k} (c d : Table k) (u : Fin 5 → Fin k) :
    0<binaryCspCount (matrix d) .nearClique (names c u) ↔ ∃ a b e f g, nine c d u a b e f g := by
  simp only [binaryCspCount,Pattern.order,assignmentSum,show (matrix d).order=k from rfl,choose_pos]
  apply exists_congr; intro a
  apply exists_congr; intro b
  apply exists_congr; intro e
  apply exists_congr; intro f
  apply exists_congr; intro g
  have one (P : Prop) [Decidable P] : (0 < (if P then 1 else 0 : Nat)) ↔ P := by by_cases h : P <;> simp [h]
  simp [satisfies,Pattern.edges,paintedArcs,names,nine,entry,one]

variable {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)

private theorem first (u : Fin 5 → Fin n) :
    ∃ v : Fin 5 → Fin n, ∀ i j, ¬(i=0 ∧ j=1) → ¬(i=1 ∧ j=0) →
      source G (u i) (u j)=targetName p (v i) (v j) := by
  let c := source G
  let d := targetName p
  have tr := RegionalPlanar.homCount_region p (Nat.zero_lt_of_lt (u 0).isLt) (fun _ => True) id id
    Function.injective_id Function.injective_id (fun z => iff_of_true ⟨z,rfl⟩ trivial) (fun z => iff_of_true ⟨z,rfl⟩ trivial)
    (matrix c) (matrix d) rfl rfl .nearClique RegionalPlanar.drawing_nearClique (names c u) rfl id
    (fun i j a b h v _ => by rw [entry,entry]; exact Iff.of_eq (congrArg (fun s => s=v) h))
  rw [homCount_eq_binaryCspCount,homCount_eq_binaryCspCount,List.map_id_fun] at tr
  have pos := (positive c c u).mpr ⟨u 0,u 1,u 2,u 3,u 4,by simp [nine]⟩
  rw [tr] at pos
  obtain ⟨a,b,e,f,g,ac,ad,ae,bc,bd,be,cd,ce,de⟩ := (positive c d u).mp pos
  let v : Fin 5 → Fin n := ![a,b,e,f,g]
  have pair (i j : Fin 5) (lt : i<j) (skip : ¬(i=0 ∧ j=1)) : c (u i) (u j)=d (v i) (v j) := by
    fin_cases i <;> fin_cases j <;> first
      | exact ac.symm | exact ad.symm | exact ae.symm | exact bc.symm | exact bd.symm | exact be.symm
      | exact cd.symm | exact ce.symm | exact de.symm | exact (skip ⟨rfl,rfl⟩).elim | exfalso; norm_num [Fin.lt_def] at lt
  refine ⟨v,fun i j ab ba => ?_⟩
  rcases lt_trichotomy i j with lt|rfl|lt
  · exact pair i j lt ab
  · by_cases lt : i<4
    · exact (SmallShore.endpoints p (pair i 4 lt (fun h => (by decide : (4 : Fin 5)≠1) h.2))).1
    · exact (SmallShore.endpoints p (pair 0 i (by omega) (by omega))).2
  · exact common_transpose p (pair j i lt (fun h => ba ⟨h.2,h.1⟩))

theorem synchronize (u : Fin 5 → Fin n) (a b : Fin 5) (ne : a≠b) :
    ∃ v : Fin 5 → Fin n, ∀ i j, ¬(i=a ∧ j=b) → ¬(i=b ∧ j=a) →
      source G (u i) (u j)=targetName p (v i) (v j) := by
  have ren : ∀ a b : Fin 5, a≠b → ∃ e : Equiv.Perm (Fin 5), e 0=a ∧ e 1=b := by native_decide
  obtain ⟨e,ea,eb⟩ := ren a b ne
  obtain ⟨w,hw⟩ := first p (u ∘ e)
  refine ⟨w ∘ e.symm,fun i j ab ba => ?_⟩
  obtain ⟨i,rfl⟩ := e.surjective i
  obtain ⟨j,rfl⟩ := e.surjective j
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hw i j
    (fun ⟨hi,hj⟩ => ab ⟨(congrArg e hi).trans ea,(congrArg e hj).trans eb⟩)
    (fun ⟨hi,hj⟩ => ba ⟨(congrArg e hi).trans eb,(congrArg e hj).trans ea⟩)

/-- The names through the third point determine the missing directed name. -/
def Forced {k} (c : Table k) (a b z : Fin k) : Prop :=
  ∀ x y t, c x t=c a z → c t y=c z b → c x y=c a b

theorem complete (u : Fin 5 → Fin n) (a b z : Fin 5) (ab : a≠b) (az : a≠z) (bz : b≠z)
    (force : Forced (source G) (u a) (u b) (u z)) :
    ∃ v : Fin 5 → Fin n, ∀ i j, source G (u i) (u j)=targetName p (v i) (v j) := by
  obtain ⟨v,hv⟩ := synchronize p u a b ab
  obtain ⟨x,y,support⟩ := StrategyColors.exists_source p (v a) (v b)
  have eq := (associated p).mpr (StrategyColors.maps_support p support)
  obtain ⟨e,he⟩ := (SixTenCoordinates.commonLaws p).middle eq
  obtain ⟨left,right⟩ := he (e.symm (v z))
  simp only [Equiv.apply_symm_apply] at left right
  have chord := (force x y (e.symm (v z))
    (left.trans (hv a z (fun h => bz h.2.symm) (fun h => ab h.1)).symm)
    (right.trans (hv z b (fun h => az h.1.symm) (fun h => ab h.2.symm)).symm)).symm.trans eq
  refine ⟨v,fun i j => ?_⟩
  by_cases h : i=a ∧ j=b
  · obtain ⟨rfl,rfl⟩ := h; exact chord
  by_cases h' : i=b ∧ j=a
  · obtain ⟨rfl,rfl⟩ := h'; exact common_transpose p chord
  exact hv i j h h'

end QGI.Coherent.LargeOrderFiveAnchors
