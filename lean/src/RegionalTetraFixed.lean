import RegionalTetraOperators

noncomputable section
namespace QGI.Coherent.RegionalTetraFixed
open Intertwiner Synchrony StrategyColorLaws SixTenCoordinates RegionalSixTwelveStats RegionalTetraLayout RegionalTetraOperators
open RegionalSixTwelveGeometry (Point)
open FourTwelveCycle (Edge edge)
open FourTwelveFunctional (source)
open private sums from Intertwiner
open private qproduct qcolumn sum_quotient from RegionalTetraOperators

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {l r v w : Nat} {F : Shore (source G) l Point} {Y : Shore (source G) r Right}
    {T : Shore (targetName p) l Point} {Z : Shore (targetName p) r Right}

theorem quotient_fixed (vw : v≠w) (P : Layout F Y v w) (Q : Layout T Z v w) :
    ∃ (ξ : cyclic p) (h : Equiv.Perm Face), ξ≠0 ∧ ∀ i, quotient p P Q i (h i) ξ=ξ := by
  classical
  let q := quotient p P Q
  have fix (s : Finset Face) : ∃ ξ : cyclic p, ξ≠0 ∧ ∀ i∈s, ∃ a, q i a ξ=ξ := by
    induction s using Finset.induction_on with
    | empty => exact ⟨⟨p.psi,psi_mem p⟩,fun h => psi_ne_zero p (congrArg Subtype.val h),by simp⟩
    | @insert i s _ ih =>
      obtain ⟨ξ,nz,old⟩ := ih
      have exist : ∃ a, q i a ξ≠0 := by
        by_contra! z
        have h := sum_quotient p P Q i ξ
        change ∑ a, q i a ξ=ξ at h
        exact nz (h.symm.trans (Finset.sum_eq_zero (fun a _ => z a)))
      obtain ⟨a,ha⟩ := exist
      refine ⟨q i a ξ,ha,fun j jp => ?_⟩
      rcases Finset.mem_insert.mp jp with rfl|prev
      · exact ⟨a,congrArg (fun e : Module.End ℂ (cyclic p) => e ξ) ((qproduct p P Q j a a).trans (if_pos rfl))⟩
      · obtain ⟨b,hb⟩ := old j prev
        have eq := congrArg (fun e : Module.End ℂ (cyclic p) => e ξ) (commutes p vw P Q j i b a).eq
        exact ⟨b,eq.trans (congrArg (q i a) hb)⟩
  obtain ⟨ξ,nz,all⟩ := fix Finset.univ
  choose h hh using fun i => all i (Finset.mem_univ _)
  have inject : Function.Injective h := by
    intro i j eq
    by_cases ne : i=j
    · exact ne
    have z := congrArg (fun e : Module.End ℂ (cyclic p) => e ξ) (qcolumn p vw P Q (h i) i j ne)
    change q i (h i) (q j (h i) ξ)=0 at z
    rw [show q j (h i) ξ=ξ by rw [eq,hh],hh] at z
    exact (nz z).elim
  exact ⟨ξ,Equiv.ofBijective h (Finite.injective_iff_bijective.mp inject),nz,hh⟩

private theorem representative (P : Layout F Y v w) (Q : Layout T Z v w) {ξ : cyclic p} {i a : Face}
    (fixed : quotient p P Q i a ξ=ξ) {x y : Fin n} (active : U p x y ξ≠0) :
    ∃ k : Slot, source G x (right P (i,0))=targetName p y (right Q (a,k)) := by
  by_contra! missed
  apply active
  calc
    _ = U p x y (quotient p P Q i a ξ) := congrArg (U p x y) fixed.symm
    _ = ∑ k : Slot, U p x y (U p (right P (i,0)) (right Q (a,k)) ξ) := by simp [quotient,LinearMap.sum_apply]
    _ = 0 := by
      apply Finset.sum_eq_zero; intro k _
      have zero : (U p x y).comp (U p (right P (i,0)) (right Q (a,k)))=0 := by
        by_contra h; exact missed k ((associated p).mpr (StrategyColors.maps_support p h))
      exact congrArg (fun e : Module.End ℂ (cyclic p) => e ξ) zero

structure Fixed (P : Layout F Y v w) (Q : Layout T Z v w) where
  ξ : cyclic p
  nz : ξ≠0
  face : Equiv.Perm Face
  point : Equiv.Perm Point
  left_fixed : ∀ i, U p (left P i) (left Q (point i)) ξ=ξ
  right_domain : ∀ j : RegionalTetraOperators.Vertex, ∀ a, U p (right P j) a ξ≠0 → ∃ k, right Q (face j.1,k)=a

theorem choose (vw : v≠w) (P : Layout F Y v w) (Q : Layout T Z v w) : Nonempty (Fixed p P Q) := by
  classical
  obtain ⟨ξ,h,nz,fixed⟩ := quotient_fixed p vw P Q
  have dom (j : RegionalTetraOperators.Vertex) (a) (act : U p (right P j) a ξ≠0) : ∃ k, right Q (h j.1,k)=a := by
    obtain ⟨⟨q,t⟩,rfl⟩ := support_right p P Q j a ξ act
    obtain ⟨s,hs⟩ := representative p P Q (fixed j.1) act
    have qeq : q=h j.1 := (classes (commonLaws p) vw P Q hs).mp rfl
    exact ⟨t,by rw [qeq]⟩
  have belongs {i j : Point} (act : U p (left P i) (left Q j) ξ≠0) (a : Face) :
      a∈edge i ↔ h a∈edge j := by
    obtain ⟨k,hit⟩ := representative p P Q (fixed a) act
    have eq := common_transpose p hit
    change color F Y (P.right (a,0)) (P.left i)=color T Z (Q.right (h a,k)) (Q.left j) at eq
    rw [P.names,Q.names] at eq
    by_cases src : a∈edge i <;> by_cases tgt : h a∈edge j <;> simp_all
  have targets (i : Point) : ∃ j, U p (left P i) (left Q j) ξ≠0 := by
    obtain ⟨a,ha⟩ := DoubledEdges.nonzero_row p ξ nz (left P i)
    obtain ⟨j,hj⟩ := (left_range Q a).mpr ((DoubledEdges.diag_of_nonzero p ha).symm.trans (F _).property)
    exact ⟨j,by rw [hj]; exact ha⟩
  choose f hf using targets
  have pins (i : Point) : U p (left P i) (left Q (f i)) ξ=ξ := by
    have one (a : Fin n) (act : U p (left P i) a ξ≠0) : a=left Q (f i) := by
      obtain ⟨t,rfl⟩ := (left_range Q a).mpr ((DoubledEdges.diag_of_nonzero p act).symm.trans (F _).property)
      have eq : edge t=edge (f i) := by
        ext z
        obtain ⟨a,rfl⟩ := h.surjective z
        exact (belongs act a).symm.trans (belongs (hf i) a)
      exact congrArg (left Q) (FourTwelveTypes.edge_inj eq)
    calc
      _ = ∑ a, U p (left P i) a ξ := (Finset.sum_eq_single (left Q (f i))
        (fun z _ ne => by by_contra act; exact ne (one z act)) (by simp)).symm
      _ = ξ := (sums p (left P i) ξ).1
  have fInj : Function.Injective f := by
    intro i j eq
    apply FourTwelveTypes.edge_inj
    ext a
    exact (belongs (hf i) a).trans (by rw [eq]; exact (belongs (hf j) a).symm)
  exact ⟨⟨ξ,nz,h,Equiv.ofBijective f (Finite.injective_iff_bijective.mp fInj),pins,dom⟩⟩

end QGI.Coherent.RegionalTetraFixed

