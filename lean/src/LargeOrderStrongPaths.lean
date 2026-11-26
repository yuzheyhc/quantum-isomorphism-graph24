import FourSixInterfaces

namespace QGI.Coherent.LargeOrderStrongPaths
open SixTenCoordinates FourSixSix
open FourSixSix.Interfaces (flag)

/-- A symmetric choice of coordinates for the incidence matrix of a cycle
on four vertices and its four edges. The bipartite graph is an eight-cycle. -/
def cycle (a b : Fin 4) := decide ((a.val+b.val)%4 < 2)

def meet {I J M : Type} [Fintype M] (a : I → M → Bool) (b : J → M → Bool) (i : I) (j : J) : Nat :=
  ∑ t, if a i t=true ∧ b j t=true then 1 else 0

def row {I J : Type} [Fintype J] (a : I → J → Nat) (i : I) (v : Nat) :=
  (Finset.univ.filter (fun j => a i j=v)).card

def regular {I J : Type} [Fintype J] (a : I → J → Nat) (base : I) :=
  ∀ i : I, ∀ v : Fin 5, row a i v.val=row a base v.val

instance {I J : Type} [Fintype I] [Fintype J] (a : I → J → Nat) (base : I) :
    Decidable (regular a base) := by unfold regular; infer_instance

/-- Two eight-cycle rectangles sharing their four-point shore either
violate regularity of a named row statistic or isolate a column. -/
theorem cycles : ∀ h : Equiv.Perm (Fin 4),
    let m := meet cycle (fun j k => cycle j (h k))
    regular m 0 → ∃ j, ∀ z, m 0 z=m 0 j → z=j := by native_decide

/-- The four-by-four cycle and the point-edge incidence of a tetrahedron
cannot share their four-point shore in a coherent configuration. The two
classes of edges of the tetrahedron have different overlap histograms. -/
theorem mixed : ∀ h : Equiv.Perm (Fin 4),
    ¬regular (meet (fun j k => flag k j) (fun j k => cycle j (h k))) 0 := by native_decide

/-- Of the 720 coordinate changes on the common six-point shore, only
the two tetrahedral orbits yield regular rows. Both isolate a column. -/
theorem tetrahedra : ∀ h : Equiv.Perm (Fin 6),
    let m := meet flag (fun j k => flag j (h k))
    regular m 0 → ∃ j, ∀ z, m 0 z=m 0 j → z=j := by native_decide

theorem path {n l r v} {c : Fin n → Fin n → Nat} {X Y M : Type}
    [Fintype Y] [Fintype M] (law : Laws c c) (F : Shore c l X) (S : Shore c r Y)
    (L R : Shore c v M) (a : X → M → Bool) (b : Y → M → Bool)
    (left : Block F F L L a a) (right : Block S S R R b b) (base : X) :
    ∃ h : Equiv.Perm M, let m := meet a (fun j k => b j (h k))
      Block F F S S m m ∧ regular m base := by
  let h := L.trans R.symm
  have eq (k : M) : atPoint R (h k)=atPoint L k := by
    simp only [h,atPoint,Equiv.trans_apply,Equiv.apply_symm_apply]
  have shift : Block S S L L (fun j k => b j (h k)) (fun j k => b j (h k)) :=
    fun ⦃i j x y⦄ hit => right (by simpa only [eq] using hit)
  let m := meet a (fun j k => b j (h k))
  have mix : Block F F S S m m :=
    Block.fold law left (Block.flip law shift) (fun u w => if u=true ∧ w=true then 1 else 0)
  refine ⟨h,mix,fun i v => ?_⟩
  have bit : Block F F S S (fun i j => decide (m i j=v.val)) (fun i j => decide (m i j=v.val)) :=
    fun ⦃_ _ _ _⦄ hit => congrArg (fun k => decide (k=v.val)) (mix hit)
  simpa only [row,decide_eq_true_eq] using Block.degree_eq law bit i base

end QGI.Coherent.LargeOrderStrongPaths
