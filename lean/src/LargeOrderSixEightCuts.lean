import LargeOrderSixEightWitnesses
import LargeOrderCycleMates
import SixSixEightPins

noncomputable section
namespace QGI.Coherent.LargeOrderSixEightCuts
open SixTenCoordinates SixEightGeometry LargeOrderEightCycles FourTwelveCycle
open SixEightCatalog (Six Eight)
open FourTwelveFunctional (source)
open SixSixEightPins (Flat)
open private count from LargeOrderSixEightWitnesses


theorem cut {n r v : Nat} {G : Graph n} (S : Shore (source G) r Six) (Y : Shore (source G) v Eight)
    (rv : r≠v) (strong : ¬SplitRectangle.Twins (rect S Y)) :
    (∀ i j, (Finset.univ.filter fun b => rect Y Y i b=rect Y Y i j).card≤3) ∨
    ∀ {l : Nat} (F : Shore (source G) l (Fin 4)), Flat S F → ¬Nonempty (CycleData F Y) := by
  classical
  obtain ⟨a,u,w,N,ls,rs,cp,sa,sy⟩ := SixEightModel.represent rv S Y
  change ∀ i j, rect S Y (u i) (w j)=N (SixEightCatalog.M a i j) at cp
  change ∀ i j, rect Y Y (w i) (w j)=N (SixEightCatalog.B a i j) at sy
  rcases SixEightCatalog.geometry a ls rs with weak|tet|cube
  · exfalso; apply strong; constructor
    · intro i b j eq t
      obtain ⟨i,rfl⟩ := u.surjective i; obtain ⟨b,rfl⟩ := u.surjective b
      obtain ⟨j,rfl⟩ := w.surjective j; obtain ⟨t,rfl⟩ := w.surjective t
      rw [cp,cp,N.injective.eq_iff] at eq ⊢
      exact Fin.ext (weak.1 i b j (congrArg Fin.val eq) t)
    · intro i j t eq b
      obtain ⟨i,rfl⟩ := u.surjective i; obtain ⟨b,rfl⟩ := u.surjective b
      obtain ⟨j,rfl⟩ := w.surjective j; obtain ⟨t,rfl⟩ := w.surjective t
      rw [cp,cp,N.injective.eq_iff] at eq ⊢
      exact Fin.ext (weak.2 i j t (congrArg Fin.val eq) b)
  · right
    intro l F flat ⟨D⟩
    let row (i : Fin 4) (j : Eight) := decide (rect F Y i j=D.mark)
    let X := fun i j => decide (rect S Y i j=N (SixEightCatalog.flag a))
    have inc : Block S S Y Y X X := fun ⦃_ _ _ _⦄ h => congrArg (fun v => decide (v=N (SixEightCatalog.flag a))) h
    have mk : Block F F Y Y row row := fun ⦃_ _ _ _⦄ h => congrArg (fun v => decide (v=D.mark)) h
    let term := fun (x y : Bool) => if x=true ∧ y=true then 1 else 0
    have prod := Block.fold (sourceLaws _) inc (Block.flip (sourceLaws _) mk) term
    have fixedRow (i : Fin 4) (j : Eight) : row i (w j)=row i (w 0) := by
      apply LargeOrderSixEightWitnesses.detect_rows a tet (fun z => row i (w z)) _ _ j
      · intro t
        obtain ⟨k,diff,one,col⟩ := LargeOrderCycleMates.mate D (w t)
        obtain ⟨k,rfl⟩ := w.surjective k
        refine ⟨k,fun h => diff (congrArg w h),?_,(congrArg (fun z => decide (z=D.mark)) (col i)).symm⟩
        intro z
        apply Eq.symm
        apply LargeOrderSixEightWitnesses.same_columns a tet t k _ z
        intro b h
        apply w.injective
        apply one
        change rect Y Y (w t) (w b)=rect Y Y (w t) (w k)
        rw [sy,sy,h]
      · have weights (q : Six) : count a (SixEightCatalog.flag a) q (fun j => row i (w j))=
             ∑ b, term (X (u q) b) (row i b) := by
          rw [←Equiv.sum_comp w (fun b => term (X (u q) b) (row i b))]
          simp only [count,term,X,cp,N.injective.eq_iff,decide_eq_true_eq]
        intro q
        rw [weights,weights]
        exact prod ((flat (u q) i).trans (flat (u 0) i).symm)
    have all (j : Eight) : edge (D.code j)=edge (D.code (w 0)) := by
      obtain ⟨j,rfl⟩ := w.surjective j
      ext i
      rw [←D.cells,←D.cells]
      exact decide_eq_decide.mp (fixedRow i j)
    have line : Function.Injective (fun i : Fin 4 => edge (cycle i)) := by native_decide
    have same (j : Eight) : D.cycle.label j=D.cycle.label (w 0) := by
      have eq := all j; rw [D.cycle.edges,D.cycle.edges] at eq
      exact line (Finset.map_injective _ eq)
    have m := D.cycle.twice (D.cycle.label (w 0))
    simp [same] at m
  · left
    intro i j
    obtain ⟨i,rfl⟩ := w.surjective i; obtain ⟨j,rfl⟩ := w.surjective j
    apply LE.le.trans (le_of_eq (count_equiv w.symm _ _ ?_)) (SixEightCatalog.cube_shore a cube i j)
    intro b; obtain ⟨b,rfl⟩ := w.surjective b
    simp only [Equiv.symm_apply_apply,sy,N.injective.eq_iff]

end QGI.Coherent.LargeOrderSixEightCuts
