import RegionalTetraOperators

noncomputable section
namespace QGI.Coherent.RepeatedTetra
open Intertwiner Synchrony StrategyColorLaws SixTenCoordinates RegionalSixTwelveStats RegionalTetraLayout
open RegionalSixTwelveGeometry (Point)
open FourTwelveCycle (Edge edge)
open FourTwelveFunctional (source)
open private commute_cell column_sums_commute all_pairs from DoubledEdges
open private sums from Intertwiner

variable {m copies : Nat} [NeZero copies]
structure Repeated (copies : Nat) {m n l r : Nat} {c : Fin n → Fin n → Nat}
    (F : Shore c l Point) (Y : Shore c r (Fin m)) (v w : Nat) where
  left : Equiv.Perm Point
  right : Face × Fin copies ≃ Fin m
  names : ∀ q k e, color F Y (right (q,k)) (left e)=if q∈edge e then v else w

abbrev left {n l r v w} {c : Fin n → Fin n → Nat} {F : Shore c l Point} {Y : Shore c r (Fin m)} (P : Repeated copies F Y v w) (i : Point) :=
  atPoint F (P.left i)
abbrev right {n l r v w} {c : Fin n → Fin n → Nat} {F : Shore c l Point} {Y : Shore c r (Fin m)} (P : Repeated copies F Y v w) (i : Face × Fin copies) :=
  atPoint Y (P.right i)

theorem right_inj {n l r v w} {c : Fin n → Fin n → Nat} {F : Shore c l Point} {Y : Shore c r (Fin m)} (P : Repeated copies F Y v w) :
    Function.Injective (right P) := Subtype.val_injective.comp (Y.injective.comp P.right.injective)

theorem right_range {n l r v w} {c : Fin n → Fin n → Nat} {F : Shore c l Point} {Y : Shore c r (Fin m)} (P : Repeated copies F Y v w) (z : Fin n) :
    (∃ i, right P i=z) ↔ c z z=r := by
  constructor
  · rintro ⟨i,rfl⟩; exact (Y _).property
  · intro h; exact ⟨P.right.symm (Y.symm ⟨z,h⟩),by simp only [right,atPoint,Equiv.apply_symm_apply]⟩

theorem left_range {n l r v w} {c : Fin n → Fin n → Nat} {F : Shore c l Point} {Y : Shore c r (Fin m)} (P : Repeated copies F Y v w) (z : Fin n) :
    (∃ i, left P i=z) ↔ c z z=l := by
  constructor
  · rintro ⟨i,rfl⟩; exact (F _).property
  · intro h; exact ⟨P.left.symm (F.symm ⟨z,h⟩),by simp only [left,atPoint,Equiv.apply_symm_apply]⟩

theorem classes {n l r v w} {c d : Fin n → Fin n → Nat} {F : Shore c l Point} {Y : Shore c r (Fin m)}
    {T : Shore d l Point} {Z : Shore d r (Fin m)} (law : Laws c d) (vw : v≠w) (P : Repeated copies F Y v w) (Q : Repeated copies T Z v w)
    {i j x y : Face × Fin copies} (same : c (right P i) (right P j)=d (right Q x) (right Q y)) : i.1=j.1 ↔ x.1=y.1 := by
  let A := P.right.trans Y
  let B := Q.right.trans Z
  let L := P.left.trans F
  let R := Q.left.trans T
  let hit := fun (x : Face × Fin copies) (e : Edge) => decide (x.1∈edge e)
  have cross : Block A B L R hit hit := by
    intro ⟨a,k⟩ e ⟨b,t⟩ f h
    change color F Y (P.right (a,k)) (P.left e)=color T Z (Q.right (b,t)) (Q.left f) at h
    rw [P.names,Q.names] at h
    by_cases ha : a∈edge e <;> by_cases hb : b∈edge f <;> simp_all [hit]
  have eq := Block.gram law cross same
  have read : ∀ a b : Face × Fin copies, Block.overlap hit a b=3 ↔ a.1=b.1 := by
    intro a b
    exact (show ∀ i j : Face, (Finset.univ.filter (fun e : Edge => decide (i∈edge e)=true ∧ decide (j∈edge e)=true)).card=3 ↔ i=j by decide) a.1 b.1
  rw [←read,←read,eq]

open RegionalTetraOperators (restrict_sum)

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {l r v w : Nat} {F : Shore (source G) l Point} {Y : Shore (source G) r (Fin m)}
    {T : Shore (targetName p) l Point} {Z : Shore (targetName p) r (Fin m)}

def quotient (P : Repeated copies F Y v w) (Q : Repeated copies T Z v w) (i a : Face) : Module.End ℂ (cyclic p) :=
  ∑ k : Fin copies, U p (right P (i,0)) (right Q (a,k))

theorem support_right (P : Repeated copies F Y v w) (Q : Repeated copies T Z v w) (j : Face × Fin copies) (a : Fin n) (ξ : cyclic p)
    (active : U p (right P j) a ξ≠0) : ∃ t, right Q t=a :=
  (right_range Q a).mpr ((DoubledEdges.diag_of_nonzero p active).symm.trans (Y _).property)

private theorem sum_quotient (P : Repeated copies F Y v w) (Q : Repeated copies T Z v w) (j : Face) (ξ : cyclic p) :
    ∑ a, quotient p P Q j a ξ=ξ := by
  have h := restrict_sum (right Q) (right_inj Q) (fun a => U p (right P (j,0)) a ξ)
    (fun a outside => by by_contra nz; exact outside (support_right p P Q _ a ξ nz))
  rw [Fintype.sum_prod_type] at h
  simpa only [quotient,LinearMap.sum_apply,←h] using (sums p (right P (j,0)) ξ).1

private theorem qproduct (P : Repeated copies F Y v w) (Q : Repeated copies T Z v w) (i a b : Face) :
    quotient p P Q i a * quotient p P Q i b = if a=b then quotient p P Q i a else 0 := by
  classical
  unfold quotient
  rw [Finset.sum_mul]
  by_cases ab : a=b
  · subst b; rw [if_pos rfl]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum,Finset.sum_eq_single k]
    · exact (restricted_projection p _ _).1
    · intro t _ ne
      exact (magic_orthogonal p _ _ _ (fun eq => ne (Prod.mk.inj ((right_inj Q) eq)).2.symm)).1
    · intro absent; exact (absent (Finset.mem_univ k)).elim
  · rw [if_neg ab]
    apply Finset.sum_eq_zero
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero; intro z _
    exact (magic_orthogonal p _ _ _ (fun eq => ab (Prod.mk.inj ((right_inj Q) eq)).1)).1

private theorem qcolumn (vw : v≠w) (P : Repeated copies F Y v w) (Q : Repeated copies T Z v w) (a i j : Face) (ne : i≠j) :
    quotient p P Q i a * quotient p P Q j a=0 := by
  unfold quotient; rw [Finset.sum_mul]
  apply Finset.sum_eq_zero; intro k _
  rw [Finset.mul_sum]; apply Finset.sum_eq_zero; intro t _
  by_contra hit
  exact ne ((classes (commonLaws p) vw P Q ((associated p).mpr (StrategyColors.maps_support p hit))).mpr rfl)

private theorem two_sum (vw : v≠w) (P : Repeated copies F Y v w) (Q : Repeated copies T Z v w) (i a b : Face) (ab : a≠b)
    (e : Edge) (he : edge e={a,b}) :
    quotient p P Q i a+quotient p P Q i b =
      ∑ z∈Finset.univ.filter (fun z => source G (right P (i,0)) z=v), U p z (left Q e) := by
  apply LinearMap.ext; intro ξ
  have law := mark_intertwines p v (right P (i,0)) (left Q e) ξ
  simp only [mark,ite_smul,one_smul,zero_smul,←Finset.sum_filter] at law
  rw [LinearMap.sum_apply]
  rw [law,Finset.sum_filter]
  have restrict := restrict_sum (right Q) (right_inj Q)
    (fun z => if targetName p z (left Q e)=v then U p (right P (i,0)) z ξ else 0)
    (fun z out => by dsimp only
                     split
                     · by_contra nz; exact out (support_right p P Q _ z ξ nz)
                     · rfl)
  rw [restrict,Fintype.sum_prod_type]
  have entry (q : Face) (k : Fin copies) : targetName p (right Q (q,k)) (left Q e)=v ↔ q∈edge e := by
    change color T Z (Q.right (q,k)) (Q.left e)=v ↔ _
    rw [Q.names]; split <;> simp_all [Ne.symm vw]
  simp only [entry,he,Finset.mem_insert,Finset.mem_singleton]
  have collapse (q : Face) : (∑ k : Fin copies, if q=a ∨ q=b then U p (right P (i,0)) (right Q (q,k)) ξ else 0)=
      if q∈({a,b} : Finset Face) then quotient p P Q i q ξ else 0 := by
    by_cases h : q=a ∨ q=b <;> simp [h,quotient,LinearMap.sum_apply]
  simp only [collapse,←Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_pair ab,LinearMap.add_apply]

theorem commutes (vw : v≠w) (P : Repeated copies F Y v w) (Q : Repeated copies T Z v w) (i j a b : Face) :
    Commute (quotient p P Q i a) (quotient p P Q j b) := by
  let q := quotient p P Q
  have row (i a b : Face) (ne : a≠b) : q i a*q i b=0 := (qproduct p P Q i a b).trans (if_neg ne)
  by_cases ij : i=j
  · subst j; by_cases ab : a=b
    · subst b; exact Commute.refl _
    · exact (row i a b ab).trans (row i b a (Ne.symm ab)).symm
  by_cases ab : a=b
  · subst b; exact (qcolumn p vw P Q a i j ij).trans (qcolumn p vw P Q a j i (Ne.symm ij)).symm
  obtain ⟨e,he⟩ := all_pairs a b ab
  apply commute_cell ((qproduct p P Q i a a).trans (if_pos rfl)) (row i a b ab) (row i b a (Ne.symm ab))
    (qcolumn p vw P Q a i j ij) (qcolumn p vw P Q a j i (Ne.symm ij))
    (qcolumn p vw P Q b i j ij) (qcolumn p vw P Q b j i (Ne.symm ij))
  rw [two_sum p vw P Q i a b ab e he,two_sum p vw P Q j a b ab e he]
  exact column_sums_commute p _ _ _

theorem quotient_fixed (vw : v≠w) (P : Repeated copies F Y v w) (Q : Repeated copies T Z v w) :
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

private theorem representative (P : Repeated copies F Y v w) (Q : Repeated copies T Z v w) {ξ : cyclic p} {i a : Face}
    (fixed : quotient p P Q i a ξ=ξ) {x y : Fin n} (active : U p x y ξ≠0) :
    ∃ k : Fin copies, source G x (right P (i,0))=targetName p y (right Q (a,k)) := by
  by_contra! missed
  apply active
  calc
    _ = U p x y (quotient p P Q i a ξ) := congrArg (U p x y) fixed.symm
    _ = ∑ k : Fin copies, U p x y (U p (right P (i,0)) (right Q (a,k)) ξ) := by simp [quotient,LinearMap.sum_apply]
    _ = 0 := by
      apply Finset.sum_eq_zero; intro k _
      have zero : (U p x y).comp (U p (right P (i,0)) (right Q (a,k)))=0 := by
        by_contra h; exact missed k ((associated p).mpr (StrategyColors.maps_support p h))
      exact congrArg (fun e : Module.End ℂ (cyclic p) => e ξ) zero

structure Fixed (P : Repeated copies F Y v w) (Q : Repeated copies T Z v w) where
  ξ : cyclic p
  nz : ξ≠0
  face : Equiv.Perm Face
  point : Equiv.Perm Point
  left_fixed : ∀ i, U p (left P i) (left Q (point i)) ξ=ξ
  right_domain : ∀ j : Face × Fin copies, ∀ a, U p (right P j) a ξ≠0 → ∃ k, right Q (face j.1,k)=a

theorem choose (vw : v≠w) (P : Repeated copies F Y v w) (Q : Repeated copies T Z v w) : Nonempty (Fixed p P Q) := by
  classical
  obtain ⟨ξ,h,nz,fixed⟩ := quotient_fixed p vw P Q
  have dom (j : Face × Fin copies) (a) (act : U p (right P j) a ξ≠0) : ∃ k, right Q (h j.1,k)=a := by
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

end QGI.Coherent.RepeatedTetra
