import SixNineModel

noncomputable section
namespace QGI.Coherent.SixNineTriples
open Relations StrategyColorLaws SixTenCoordinates SmallUnion SmallFiberExtension
open FourTwelveFunctional (source fiber_eq)
open RegionalCycleExtension (emb range_emb)
open private induce from SmallUnionRealization

/-- Named rectangle shapes needed on a six- and a nine-point
shore. The local input is obtained by inducing the original configuration. -/
theorem classify {n : Nat} {G : Graph n} {r s : Nat} (apart : r≠s)
    (S : Shore (source G) r (Fin 6)) (Y : Shore (source G) s (Fin 9))
    (dup : ∃ i j, i≠j ∧ ∀ t, source G (atPoint S i) (atPoint Y t)=source G (atPoint S j) (atPoint Y t)) :
    let N := fun i j => source G (atPoint S i) (atPoint Y j)
    (∀ i j, N i j=N 0 0) ∨ ∃ (v : Nat) (A : Fin 6 → Fin 3) (B : Fin 9 → Fin 3),
        Function.Surjective A ∧ Function.Surjective B ∧ (∀ i j, N i j=v ↔ A i=B j) ∧
        ∀ j k, B j=B k → ∀ i, N i j=N i k := by
  classical
  let N := fun i j => source G (atPoint S i) (atPoint Y j)
  obtain ⟨a,u,w,labels,ls,rs,cells,_⟩ := SixNineModel.represent apart S Y
  change ∀ i j, N (u i) (w j)=labels (SixNineCatalog.M a i j) at cells
  obtain ⟨i,j,ij,same⟩ := dup
  have duplicate : ∃ i j, i≠j ∧ ∀ t, SixNineCatalog.M a i t=SixNineCatalog.M a j t := by
    refine ⟨u.symm i,u.symm j,u.symm.injective.ne ij,fun t => labels.injective ?_⟩
    rw [←cells,←cells,Equiv.apply_symm_apply,Equiv.apply_symm_apply]; exact same (w t)
  rcases SixNineCatalog.alternatives a ls rs duplicate with all|⟨ontoA,ontoB,hit,keeps⟩
  · left
    have constant (i j) : N i j=labels (SixNineCatalog.M a 0 0) := by
      obtain ⟨i,rfl⟩ := u.surjective i; obtain ⟨j,rfl⟩ := w.surjective j
      exact (cells i j).trans (congrArg labels (all i j))
    exact fun i j => (constant i j).trans (constant 0 0).symm
  · right
    refine ⟨labels (SixNineCatalog.flag a),SixNineCatalog.rowClass a ∘ u.symm,SixNineCatalog.colClass a ∘ w.symm,
      Function.Surjective.comp (f:=u.symm) ontoA u.symm.surjective,Function.Surjective.comp (f:=w.symm) ontoB w.symm.surjective,?_,?_⟩
    · intro i j
      obtain ⟨i,rfl⟩ := u.surjective i; obtain ⟨j,rfl⟩ := w.surjective j
      change N (u i) (w j)=_ ↔ _
      rw [cells,labels.injective.eq_iff]
      simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hit i j
    · intro j k h i
      obtain ⟨j,rfl⟩ := w.surjective j; obtain ⟨k,rfl⟩ := w.surjective k; obtain ⟨i,rfl⟩ := u.surjective i
      change N (u i) (w j)=N (u i) (w k)
      rw [cells,cells]
      exact congrArg labels (keeps j k (by simpa only [Function.comp_apply,Equiv.symm_apply_apply] using h) i)

end QGI.Coherent.SixNineTriples
