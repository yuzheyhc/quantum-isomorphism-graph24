import SixNineGridCatalog
import SixNineModel
import SixEightGeometry

noncomputable section
namespace QGI.Coherent.SixNineGridGeometry
open SixTenCoordinates SixEightGeometry
open FourTwelveFunctional (source)

structure Triple {n l r : Nat} {c : Fin n → Fin n → Nat} (S : Shore c l (Fin 6)) (Y : Shore c r (Fin 9)) where
  mark : Nat
  a : Fin 6 → Fin 3
  b : Fin 9 → Fin 3
  aSize : ∀ t, (Finset.univ.filter (fun i => a i=t)).card=2
  bSize : ∀ t, (Finset.univ.filter (fun i => b i=t)).card=3
  flag : ∀ i j, rect S Y i j=mark ↔ a i=b j
  uniform : ∀ j k, b j=b k → ∀ i, rect S Y i j=rect S Y i k

def HasFour {n r : Nat} {c : Fin n → Fin n → Nat} (Y : Shore c r (Fin 9)) := ∃ g : Fin 9 → Fin 9 → Bool,
  (∀ i, g i i=false) ∧ (∀ i j, g i j=g j i) ∧ (∀ i, FiberRectangles.degree (g i)=4) ∧ Block Y Y Y Y g g

theorem classify {n l r : Nat} {G : Graph n} (diff : l≠r) (S : Shore (source G) l (Fin 6)) (Y : Shore (source G) r (Fin 9)) :
    (∀ i j, rect S Y i j=rect S Y 0 0) ∨ Nonempty (Triple S Y) ∨
    (HasFour Y ∧ ∀ i k, (∀ j, rect S Y i j=rect S Y k j) → i=k) := by
  classical
  obtain ⟨x,u,w,N,ls,rs,hit,_⟩ := SixNineModel.represent diff S Y
  have cp (i j) : rect S Y (u i) (w j)=N (SixNineCatalog.M x i j) := hit i j
  rcases SixNineGridCatalog.classify x ls rs with flat|⟨ac,bc,flag,uniform⟩|⟨simple,symm,degree,unique⟩
  · left
    have constant (i j) : rect S Y i j=N (SixNineCatalog.M x 0 0) := by
      obtain ⟨i,rfl⟩ := u.surjective i; obtain ⟨j,rfl⟩ := w.surjective j
      exact (cp i j).trans (congrArg N (flat i j))
    exact fun i j => (constant i j).trans (constant 0 0).symm
  · right; left
    refine ⟨⟨N (SixNineGridCatalog.z x),SixNineGridCatalog.A x ∘ u.symm,SixNineGridCatalog.B x ∘ w.symm,?_,?_,?_,?_⟩⟩
    · intro t; exact (count_equiv u.symm _ _ (fun _ => Iff.rfl)).trans (ac t)
    · intro t; exact (count_equiv w.symm _ _ (fun _ => Iff.rfl)).trans (bc t)
    · intro i j; obtain ⟨i,rfl⟩ := u.surjective i; obtain ⟨j,rfl⟩ := w.surjective j
      simpa only [Function.comp_apply,Equiv.symm_apply_apply,cp,N.injective.eq_iff] using flag i j
    · intro j k eq i
      obtain ⟨j,rfl⟩ := w.surjective j; obtain ⟨k,rfl⟩ := w.surjective k; obtain ⟨i,rfl⟩ := u.surjective i
      exact (cp i j).trans ((congrArg N (uniform j k (by simpa only [Function.comp_apply,Equiv.symm_apply_apply] using eq) i)).trans (cp i k).symm)
  · right; right; constructor
    · let D := SixNineGridCatalog.incidence x
      have inc : Block (w.trans Y) (w.trans Y) (u.trans S) (u.trans S) D D := by
        intro i j a b h
        have tr : rect S Y (u j) (w i)=rect S Y (u b) (w a) := Relations.transpose _ h
        exact congrArg (fun z => decide (z=SixNineGridCatalog.gridMark x)) (N.injective ((cp j i).symm.trans (tr.trans (cp b a))))
      let g (i j : Fin 9) := SixNineGridCatalog.rook x (w.symm i) (w.symm j)
      refine ⟨g,fun i => simple _,fun i j => symm _ _,fun i => ?_,?_⟩
      · exact (count_equiv w.symm _ _ (fun _ => Iff.rfl)).trans (degree (w.symm i))
      · intro i j a b h
        obtain ⟨i,rfl⟩ := w.surjective i; obtain ⟨j,rfl⟩ := w.surjective j
        obtain ⟨a,rfl⟩ := w.surjective a; obtain ⟨b,rfl⟩ := w.surjective b
        simp only [g,Equiv.symm_apply_apply,SixNineGridCatalog.rook]
        exact congrArg (fun z => decide (z=1)) (Block.gram (sourceLaws _) inc h)
    · intro i k eq
      obtain ⟨i,rfl⟩ := u.surjective i; obtain ⟨k,rfl⟩ := u.surjective k
      exact congrArg u (unique i k (fun j => N.injective ((cp i j).symm.trans ((eq (w j)).trans (cp k j)))))

end QGI.Coherent.SixNineGridGeometry
