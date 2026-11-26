import SixEightGeometry

noncomputable section
namespace QGI.Coherent.DoubleTetraExclusion
open SixTenCoordinates SixEightGeometry RepeatedTetra
open FourTwelveCycle (Edge edge)
open RegionalTetraLayout (Face)
open FourTwelveFunctional (source)
open SixEightCatalog (Six Eight)

private def score (s : Face × Fin 2 → Face) (i j : Edge) : Nat :=
  ∑ x : Face × Fin 2, if x.1∈edge i ∧ s x∈edge j then 1 else 0

/-- With two copies of each face, two tetrahedral incidence systems have
at least two distinct edge-to-edge intersection numbers. -/
private theorem different : ∀ s : Face × Fin 2 → Face, ¬ ∀ i j, score s i j=score s 0 0 := by
  native_decide

theorem exclude {n l r z v w h k : Nat} {G : Graph n}
    (A : Shore (source G) l Six) (B : Shore (source G) r Six) (Y : Shore (source G) z Eight)
    (vw : v≠w) (hk : h≠k) (P : Repeated 2 A Y v w) (Q : Repeated 2 B Y h k)
    (flat : ∀ i j, rect A B i j=rect A B 0 0) : False := by
  let L := P.left.trans A
  let M := P.right.trans Y
  let R := Q.left.trans B
  let s (x : Face × Fin 2) := (Q.right.symm (P.right x)).1
  let first := fun (x : Face × Fin 2) (i : Edge) => decide (x.1∈edge i)
  let second := fun (x : Face × Fin 2) (j : Edge) => decide (s x∈edge j)
  have left : Block M M L L first first := by
    intro ⟨a,t⟩ i ⟨b,u⟩ j eq
    change RegionalSixTwelveStats.color A Y (P.right (a,t)) (P.left i)=RegionalSixTwelveStats.color A Y (P.right (b,u)) (P.left j) at eq
    rw [P.names,P.names] at eq
    by_cases ai : a∈edge i <;> by_cases bj : b∈edge j <;> simp_all [first]
  have row (x : Face × Fin 2) (i : Edge) : rect Y B (P.right x) (Q.left i)=if s x∈edge i then h else k := by
    let b := Q.right.symm (P.right x)
    have eq := Q.names b.1 b.2 i
    change rect Y B (Q.right (b.1,b.2)) (Q.left i)=_ at eq
    simpa only [Prod.mk.eta,b,Equiv.apply_symm_apply] using eq
  have right : Block M M R R second second := by
    intro x i y j eq
    change rect Y B (P.right x) (Q.left i)=rect Y B (P.right y) (Q.left j) at eq
    rw [row,row] at eq
    by_cases ai : s x∈edge i <;> by_cases bj : s y∈edge j <;> simp_all [second]
  apply different s
  intro i j
  have hit := Block.fold (sourceLaws _) (Block.flip (sourceLaws _) left) right
    (fun a b => if a=true ∧ b=true then 1 else 0)
    ((flat (P.left i) (Q.left j)).trans (flat (P.left 0) (Q.left 0)).symm)
  simpa only [first,second,score,decide_eq_true_eq] using hit

end QGI.Coherent.DoubleTetraExclusion
