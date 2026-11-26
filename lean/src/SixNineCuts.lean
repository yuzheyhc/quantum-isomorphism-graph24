import SixNineTriples

namespace QGI.Coherent.SixNineCuts
open QGI.Fifteen SixTenCoordinates
open SixNineCatalog
open FourTwelveFunctional (source)

private def side (a : Index) (i : Fin 6) := (if a.val<180 then 7 else 21 : Nat).testBit i.val

attribute [local irreducible] row model rank rows15
private theorem checked : ∀ a : Index, diagSize a (left 0)=6 → diagSize a (right 0)=9 →
    ¬(∃ i j, i≠j ∧ ∀ t, M a i t=M a j t) →
    (∀ t, ∃ i, side a i=t) ∧ ∀ i j x y,
       value a (left i) (left j)=value a (left x) (left y) →
       decide (side a i=side a j)=decide (side a x=side a y) := by native_decide

/-- When the six rows of a six-by-nine rectangle are all different, its
six-point fiber already names a nontrivial bipartition of its own points. -/
theorem cut {n l r} {G : Graph n} (apart : l≠r) (S : Shore (source G) l (Fin 6)) (Y : Shore (source G) r (Fin 9))
    (distinct : ¬∃ i j, i≠j ∧ ∀ t, source G (atPoint S i) (atPoint Y t)=source G (atPoint S j) (atPoint Y t)) :
    ∃ s : Fin 6 → Bool, Function.Surjective s ∧ Block S S S S (fun i j => decide (s i=s j)) (fun i j => decide (s i=s j)) := by
  obtain ⟨a,u,w,name,ls,rs,cells,internal⟩ := SixNineModel.represent apart S Y
  have dup : ¬∃ i j, i≠j ∧ ∀ t, M a i t=M a j t := by
    rintro ⟨i,j,ne,h⟩
    apply distinct; refine ⟨u i,u j,u.injective.ne ne,fun t => ?_⟩
    obtain ⟨t,rfl⟩ := w.surjective t
    exact (cells i t).trans ((congrArg name (h t)).trans (cells j t).symm)
  obtain ⟨onto,pres⟩ := checked a ls rs dup
  refine ⟨side a ∘ u.symm,Function.Surjective.comp (f:=u.symm) onto u.symm.surjective,?_⟩
  intro i j x y hit
  obtain ⟨i,rfl⟩ := u.surjective i; obtain ⟨j,rfl⟩ := u.surjective j
  obtain ⟨x,rfl⟩ := u.surjective x; obtain ⟨y,rfl⟩ := u.surjective y
  rw [internal,internal,name.injective.eq_iff] at hit
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using pres i j x y hit

/-- A named bipartition of a six-point fiber forces every binary
rectangle of odd column degree on that fiber to have twin rows and columns. -/
theorem even_rectangle {n l r k} [NeZero (2*k)] {G : Graph n} (S : Shore (source G) l (Fin 6))
    (F : Shore (source G) r (Fin (2*k))) (side : Fin 6 → Bool) (sur : Function.Surjective side)
    (coh : Block S S S S (fun i j => decide (side i=side j)) (fun i j => decide (side i=side j)))
    (bound : ∀ x y : Nat, 0<x → 6*x=(2*k)*y → k≤x) :
    SplitRectangle.Twins (fun i j => source G (atPoint S i) (atPoint F j)) := by
  classical
  rcases OddHalfPartition.palette (p:=k) (sourceLaws (closure G)) S F bound with ⟨z,all⟩|⟨z,w,zw,pal,rows⟩
  · exact ⟨fun i x _ _ j => (all i j).trans (all x j).symm,fun _ j t _ i => (all i j).trans (all i t).symm⟩
  let B := fun i j => decide (source G (atPoint S i) (atPoint F j)=z)
  have named : Block S S F F B B := fun ⦃_ _ _ _⦄ h => congrArg (fun x => decide (x=z)) h
  have rd (i) : FiberRectangles.degree (B i)=k := by simpa only [FiberRectangles.degree,B,decide_eq_true_eq] using rows i
  have cd (j) := Block.degree_eq (sourceLaws (closure G)) (Block.flip (sourceLaws _) named) j 0
  have balance := FiberRectangles.balance B rd cd
  let d := FiberRectangles.degree (fun i => B i 0)
  have eq : k*6=k*(2*d) := calc
    _ = 6*k := Nat.mul_comm _ _
    _ = (2*k)*d := balance
    _ = _ := by ac_rfl
  have kp : 0<k := by have := NeZero.ne (2*k); omega
  have even := Nat.eq_of_mul_eq_mul_left kp eq
  have three (j) : (Finset.univ.filter (fun i => source G (atPoint S i) (atPoint F j)=z)).card=3 := by
    have degree : FiberRectangles.degree (fun i => B i j)=3 := (cd j).trans (show d=3 by omega)
    simpa only [B,FiberRectangles.degree,decide_eq_true_eq] using degree
  exact OddHalfPartition.rigid (a:=1) (sourceLaws _) S F side sur coh z w zw pal three

end QGI.Coherent.SixNineCuts
