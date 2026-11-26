import RegionalTetraLayout

noncomputable section
namespace QGI.Coherent.RegionalTetraOperators
open Intertwiner Synchrony StrategyColorLaws SixTenCoordinates RegionalSixTwelveStats RegionalTetraLayout
open RegionalSixTwelveGeometry (Point)
open FourTwelveCycle (Edge edge)
open FourTwelveFunctional (source)
open private commute_cell column_sums_commute all_pairs from DoubledEdges
open private sums from Intertwiner

abbrev Vertex := Face × Slot

abbrev left {n l r v w} {c : Fin n → Fin n → Nat} {F : Shore c l Point} {Y : Shore c r Right} (P : Layout F Y v w) (i : Point) :=
  atPoint F (P.left i)
abbrev right {n l r v w} {c : Fin n → Fin n → Nat} {F : Shore c l Point} {Y : Shore c r Right} (P : Layout F Y v w) (i : Vertex) :=
  atPoint Y (P.right i)

theorem right_inj {n l r v w} {c : Fin n → Fin n → Nat} {F : Shore c l Point} {Y : Shore c r Right} (P : Layout F Y v w) :
    Function.Injective (right P) := Subtype.val_injective.comp (Y.injective.comp P.right.injective)

theorem right_range {n l r v w} {c : Fin n → Fin n → Nat} {F : Shore c l Point} {Y : Shore c r Right} (P : Layout F Y v w) (z : Fin n) :
    (∃ i, right P i=z) ↔ c z z=r := by
  constructor
  · rintro ⟨i,rfl⟩; exact (Y _).property
  · intro h; exact ⟨P.right.symm (Y.symm ⟨z,h⟩),by simp only [right,atPoint,Equiv.apply_symm_apply]⟩

theorem left_range {n l r v w} {c : Fin n → Fin n → Nat} {F : Shore c l Point} {Y : Shore c r Right} (P : Layout F Y v w) (z : Fin n) :
    (∃ i, left P i=z) ↔ c z z=l := by
  constructor
  · rintro ⟨i,rfl⟩; exact (F _).property
  · intro h; exact ⟨P.left.symm (F.symm ⟨z,h⟩),by simp only [left,atPoint,Equiv.apply_symm_apply]⟩

theorem classes {n l r v w} {c d : Fin n → Fin n → Nat} {F : Shore c l Point} {Y : Shore c r Right}
    {T : Shore d l Point} {Z : Shore d r Right} (law : Laws c d) (vw : v≠w) (P : Layout F Y v w) (Q : Layout T Z v w)
    {i j x y : Vertex} (same : c (right P i) (right P j)=d (right Q x) (right Q y)) : i.1=j.1 ↔ x.1=y.1 := by
  let A := P.right.trans Y
  let B := Q.right.trans Z
  let L := P.left.trans F
  let R := Q.left.trans T
  let hit := fun (x : Vertex) (e : Edge) => decide (x.1∈edge e)
  have cross : Block A B L R hit hit := by
    intro ⟨a,k⟩ e ⟨b,t⟩ f h
    change color F Y (P.right (a,k)) (P.left e)=color T Z (Q.right (b,t)) (Q.left f) at h
    rw [P.names,Q.names] at h
    by_cases ha : a∈edge e <;> by_cases hb : b∈edge f <;> simp_all [hit]
  have eq := Block.gram law cross same
  have read : ∀ a b : Vertex, Block.overlap hit a b=3 ↔ a.1=b.1 := by dsimp [hit,Block.overlap]; decide
  rw [←read,←read,eq]

theorem restrict_sum {K X M : Type} [Fintype K] [Fintype X] [AddCommMonoid M] (f : X → K) (inj : Function.Injective f)
    (term : K → M) (zero : ∀ z, (¬∃ x, f x=z) → term z=0) : ∑ z, term z=∑ x, term (f x) := by
  classical
  let e : X ↪ K := ⟨f,inj⟩
  calc
    _ = ∑ z ∈ (Finset.univ.map e), term z := Eq.symm (Finset.sum_subset (Finset.subset_univ _)
      (fun z _ h => zero z (fun ⟨x,hx⟩ => h (Finset.mem_map.mpr ⟨x,Finset.mem_univ _,hx⟩))))
    _ = _ := Finset.sum_map .. 

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {l r v w : Nat} {F : Shore (source G) l Point} {Y : Shore (source G) r Right}
    {T : Shore (targetName p) l Point} {Z : Shore (targetName p) r Right}

def quotient (P : Layout F Y v w) (Q : Layout T Z v w) (i a : Face) : Module.End ℂ (cyclic p) :=
  ∑ k : Slot, U p (right P (i,0)) (right Q (a,k))

theorem support_right (P : Layout F Y v w) (Q : Layout T Z v w) (j : Vertex) (a : Fin n) (ξ : cyclic p)
    (active : U p (right P j) a ξ≠0) : ∃ t, right Q t=a :=
  (right_range Q a).mpr ((DoubledEdges.diag_of_nonzero p active).symm.trans (Y _).property)

private theorem sum_quotient (P : Layout F Y v w) (Q : Layout T Z v w) (j : Face) (ξ : cyclic p) :
    ∑ a, quotient p P Q j a ξ=ξ := by
  have h := restrict_sum (right Q) (right_inj Q) (fun a => U p (right P (j,0)) a ξ)
    (fun a outside => by by_contra nz; exact outside (support_right p P Q _ a ξ nz))
  rw [Fintype.sum_prod_type] at h
  simpa only [quotient,LinearMap.sum_apply,←h] using (sums p (right P (j,0)) ξ).1

private theorem qproduct (P : Layout F Y v w) (Q : Layout T Z v w) (i a b : Face) :
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

private theorem qcolumn (vw : v≠w) (P : Layout F Y v w) (Q : Layout T Z v w) (a i j : Face) (ne : i≠j) :
    quotient p P Q i a * quotient p P Q j a=0 := by
  unfold quotient; rw [Finset.sum_mul]
  apply Finset.sum_eq_zero; intro k _
  rw [Finset.mul_sum]; apply Finset.sum_eq_zero; intro t _
  by_contra hit
  exact ne ((classes (commonLaws p) vw P Q ((associated p).mpr (StrategyColors.maps_support p hit))).mpr rfl)

private theorem two_sum (vw : v≠w) (P : Layout F Y v w) (Q : Layout T Z v w) (i a b : Face) (ab : a≠b)
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
  have entry (q : Face) (k : Slot) : targetName p (right Q (q,k)) (left Q e)=v ↔ q∈edge e := by
    change color T Z (Q.right (q,k)) (Q.left e)=v ↔ _
    rw [Q.names]; split <;> simp_all [Ne.symm vw]
  simp only [entry,he,Finset.mem_insert,Finset.mem_singleton]
  have collapse (q : Face) : (∑ k : Slot, if q=a ∨ q=b then U p (right P (i,0)) (right Q (q,k)) ξ else 0)=
      if q∈({a,b} : Finset Face) then quotient p P Q i q ξ else 0 := by
    by_cases h : q=a ∨ q=b <;> simp [h,quotient,LinearMap.sum_apply]
  simp only [collapse,←Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_pair ab,LinearMap.add_apply]

theorem commutes (vw : v≠w) (P : Layout F Y v w) (Q : Layout T Z v w) (i j a b : Face) :
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

end QGI.Coherent.RegionalTetraOperators

