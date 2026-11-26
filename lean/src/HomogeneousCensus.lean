import CoherentHomogeneous
import HomogeneousUnions
import SmallBlockCatalog

noncomputable section

namespace QGI
namespace Coherent

open Homogeneous.Unions (Table colorAt rawTables)

/-- For a homogeneous coherent algebra the rank is the number of basis
relations, whose positive integer valencies sum to the number of vertices.
Thus rank equal to the order means that every valency is one (a thin scheme). -/
def CoherentAlgebra.IsThin {n : Nat} (C : CoherentAlgebra n) : Prop :=
  Module.finrank ℂ C.space = n

/-- Restrict the coherent isomorphism to its actual domain and codomain. -/
def AlgebraIso.linearEquiv {n : Nat} {C D : CoherentAlgebra n} (e : AlgebraIso C D) :
    C.space ≃ₗ[ℂ] D.space := by
  let f : C.space →ₗ[ℂ] D.space := {
    toFun := fun x => ⟨e.map x.val, e.mapsTo x.val x.property⟩
    map_add' := fun x y => Subtype.ext (e.map_add _ x.property _ y.property)
    map_smul' := fun c x => Subtype.ext (e.map_smul c _ x.property) }
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    exact e.injectiveOn _ x.property _ y.property (congrArg Subtype.val h)
  · intro y
    obtain ⟨M, hM, eq⟩ := e.surjectiveOn y.val y.property
    exact ⟨⟨M, hM⟩, Subtype.ext eq⟩

theorem AlgebraIso.thin_iff {n : Nat} {C D : CoherentAlgebra n} (e : AlgebraIso C D) :
    C.IsThin ↔ D.IsThin := by
  unfold CoherentAlgebra.IsThin
  rw [e.linearEquiv.finrank_eq]

private def rowAt {n : Nat} (C : CoherentAlgebra n) (o : Fin n) :
    C.space →ₗ[ℂ] (Fin n → ℂ) where
  toFun M := M.val o
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The diagonal of M M* records the squared norms of the rows. Homogeneity
forces those norms to agree, so a single zero row forces M to vanish. -/
private theorem rowAt_injective {n : Nat} {C : CoherentAlgebra n}
    (hom : C.Homogeneous) (o : Fin n) : Function.Injective (rowAt C o) := by
  classical
  open scoped ComplexOrder in
    apply (injective_iff_map_eq_zero _).mpr
    intro M zeroRow
    obtain ⟨a, diag⟩ := hom _ (C.mul_mem M.property (C.adjoint_mem M.property))
    have normRow (i : Fin n) : dotProduct (M.val i) (star (M.val i)) = a := by
      have h := congrFun (congrFun diag i) i
      simpa [schur, Matrix.mul_apply, dotProduct, Matrix.conjTranspose_apply] using h
    change M.val o = 0 at zeroRow
    have zeroScalar := normRow o
    rw [zeroRow] at zeroScalar
    have ha : a = 0 := by simpa using zeroScalar.symm
    apply Subtype.ext
    ext i j
    exact congrFun (dotProduct_self_star_eq_zero.mp ((normRow i).trans ha)) j

/-- In a thin scheme, evaluating a fixed row is a linear isomorphism onto
all row vectors. Transfer the coordinate indicators across the algebra
isomorphism, then multiply by each indicator to read off every matrix row. -/
theorem AlgebraIso.realized_of_thin {n : Nat} (hn : 0 < n)
    {C D : CoherentAlgebra n} (hC : C.Homogeneous) (ht : C.IsThin)
    (e : AlgebraIso C D) : e.Realized := by
  classical
  let o : Fin n := ⟨0, hn⟩
  have inj := rowAt_injective hC o
  have dims : Module.finrank ℂ C.space = Module.finrank ℂ (Fin n → ℂ) := by
    simpa only [Module.finrank_fin_fun] using ht
  have onto := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dims).mp inj
  choose P hP using fun i : Fin n => onto (fun j => if j = i then (1 : ℂ) else 0)
  have rowP (i j : Fin n) : (P i).val o j = if j = i then 1 else 0 := congrFun (hP i) j
  have nonzero (i : Fin n) : ∃ j, e.map (P i).val o j ≠ 0 := by
    by_contra! h
    have z : e.linearEquiv (P i) = 0 := rowAt_injective (e.homogeneous_target hC) o (funext h)
    have vanished : P i = 0 := e.linearEquiv.map_eq_zero_iff.mp z
    have at_i := rowP i i
    rw [vanished] at at_i
    simp at at_i
  choose f hf using nonzero
  have transfer (M : Mat n) (hm : M ∈ C.space) (i : Fin n) : M o i = e.map M o (f i) := by
    have h : schur (P i).val M = M o i • (P i).val := by
      apply congrArg Subtype.val (inj (a₁ := ⟨_, C.schur_mem (P i).property hm⟩)
        (a₂ := ⟨_, C.space.smul_mem _ (P i).property⟩) ?_)
      funext j
      change (P i).val o j * M o j = M o i * (P i).val o j
      rw [rowP]
      split_ifs with eq
      · simp [eq]
      · simp
    have hmap := congrArg e.map h
    rw [e.map_schur _ (P i).property _ hm, e.map_smul _ _ (P i).property] at hmap
    have entry := congrFun (congrFun hmap o) (f i)
    change e.map (P i).val o (f i) * e.map M o (f i) = M o i * e.map (P i).val o (f i) at entry
    rw [mul_comm (M o i)] at entry
    exact (mul_left_cancel₀ (hf i) entry).symm
  have fi : Function.Injective f := by
    intro i j eq
    have h := ((transfer _ (P i).property i).trans (eq ▸ (transfer _ (P i).property j).symm))
    by_contra ne
    simp [rowP, Ne.symm ne] at h
  let perm := Equiv.ofBijective f ⟨fi, Finite.surjective_of_injective fi⟩
  refine ⟨perm, ?_⟩
  intro M hm i j
  have h := transfer _ (C.mul_mem (P i).property hm) j
  rw [e.map_mul _ (P i).property _ hm] at h
  simp only [Matrix.mul_apply] at h
  rw [← Equiv.sum_comp perm (fun z => e.map (P i).val o z * e.map M z (f j))] at h
  change (∑ z, (P i).val o z * M z j) =
    ∑ z, e.map (P i).val o (f z) * e.map M (f z) (f j) at h
  simpa [← transfer _ (P i).property, rowP, ite_mul] using h

/-- In these coordinates the entries of every algebra element are constant
on each color in the raw scheme matrix. -/
def HasTableLabel {n : Nat} (C : CoherentAlgebra n) (t : Table) : Prop :=
  ∃ f : Fin n ≃ Fin n, ∀ M ∈ C.space, ∀ x y z w : Fin n,
    colorAt t x.val y.val = colorAt t z.val w.val → M (f x) (f y) = M (f z) (f w)

end Coherent

namespace Literature
open Coherent
open Homogeneous.Unions (colorAt rawTables)

/-- The homogeneous thin case of Muzychuk–Ponomarenko, Theorem 8.1. -/
theorem muzychukPonomarenko_thin_separable {n : Nat} (hn : 0 < n)
    {C D : CoherentAlgebra n} (hC : C.Homogeneous) (ht : C.IsThin)
    (e : AlgebraIso C D) : e.Realized := e.realized_of_thin hn hC ht

/-- An explicit basic-relation table for the algebra in the
rank-two or imprimitive rank-three family. -/
def HasSmallBlockTable {n : Nat} [NeZero n] (C : CoherentAlgebra n) : Prop :=
  ∃ c : RowCensus.Table n Nat, RowCensus.Laws c ∧
    ((RowCensus.palette c).card≤2 ∨ ((RowCensus.palette c).card≤3 ∧ Nonempty (RowCensus.Imprimitivity c))) ∧
    ∀ M : Mat n, M∈C.space ↔ ∀ i j x y, c i j=c x y → M i j=M x y

/-- The residual Hanaki–Miyamoto classification of homogeneous nonthin schemes,
specialized to orders 16 and 18, in the authors' relation-matrix coordinates.
The algebra is exactly the space of complex matrices constant on those classes.
Rank two and imprimitive rank three are independently covered below.
The archive omits thin schemes and contains directed as well as symmetric relations.
Orders 16 and 17: https://doi.org/10.2206/kyushujm.52.383
Orders 18 and 19: https://doi.org/10.1007/BF03008881
Author's digital tables, as03-30.zip: https://doi.org/10.5281/zenodo.3627736 -/
axiom hanakiMiyamoto_residual_census {n : Nat} [NeZero n] (hn : n = 16 ∨ n = 18)
    (C : CoherentAlgebra n) (hC : C.Homogeneous) (ht : ¬ C.IsThin) (remaining : ¬ HasSmallBlockTable C) :
    ∃ t ∈ rawTables n, ∃ f : Fin n ≃ Fin n, ∀ M : Mat n,
      M ∈ C.space ↔ ∀ x y z w : Fin n,
        colorAt t x.val y.val = colorAt t z.val w.val → M (f x) (f y) = M (f z) (f w)

theorem hanakiMiyamoto_nonthin_census {n : Nat} (hn : n = 16 ∨ n = 18)
    (C : CoherentAlgebra n) (hC : C.Homogeneous) (ht : ¬ C.IsThin) :
    ∃ t ∈ rawTables n, ∃ f : Fin n ≃ Fin n, ∀ M : Mat n,
      M ∈ C.space ↔ ∀ x y z w : Fin n,
        colorAt t x.val y.val = colorAt t z.val w.val → M (f x) (f y) = M (f z) (f w) := by
  letI : NeZero n := ⟨by rcases hn with rfl|rfl <;> decide⟩
  by_cases known : HasSmallBlockTable C
  · obtain ⟨c,law,small,space⟩ := known
    obtain ⟨t,mem,f,he⟩ := RowCensus.small_block_catalog hn c law small
    refine ⟨t,mem,f,fun M => (space M).trans ⟨?_,?_⟩⟩
    · intro same x y z w eq
      exact same _ _ _ _ ((he _ _ _ _).mp eq)
    · intro same x y z w eq
      obtain ⟨i,rfl⟩ := f.surjective x
      obtain ⟨j,rfl⟩ := f.surjective y
      obtain ⟨k,rfl⟩ := f.surjective z
      obtain ⟨l,rfl⟩ := f.surjective w
      exact same i j k l ((he _ _ _ _).mpr eq)
  · exact hanakiMiyamoto_residual_census hn C hC ht known

end Literature

namespace Coherent
open Homogeneous.Unions (rawTables)

private theorem labelled_of_nonthin {n : Nat} (hn : n = 16 ∨ n = 18)
    {C : CoherentAlgebra n} (hC : C.Homogeneous) (ht : ¬ C.IsThin) :
    ∃ t ∈ rawTables n, HasTableLabel C t := by
  obtain ⟨t, listed, f, coordinates⟩ := Literature.hanakiMiyamoto_nonthin_census hn C hC ht
  exact ⟨t, listed, f, fun M hM => (coordinates M).mp hM⟩

/-- The thin case already supplies a point map. In the nonthin case both
algebras have certified positions in the source census up to relabelling. -/
theorem realized_or_tables {n : Nat} (hn : n = 16 ∨ n = 18) {C D : CoherentAlgebra n}
    (hC : C.Homogeneous) (e : AlgebraIso C D) :
    e.Realized ∨ ((∃ t ∈ rawTables n, HasTableLabel C t) ∧
      (∃ t ∈ rawTables n, HasTableLabel D t)) := by
  by_cases ht : C.IsThin
  · exact Or.inl (Literature.muzychukPonomarenko_thin_separable (by omega) hC ht e)
  · exact Or.inr ⟨labelled_of_nonthin hn hC ht,
      labelled_of_nonthin hn (e.homogeneous_target hC) (fun h => ht (e.thin_iff.mpr h))⟩

end Coherent
end QGI
