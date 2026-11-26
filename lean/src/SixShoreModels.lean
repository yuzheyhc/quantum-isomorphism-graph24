import SixPointCoverage

namespace QGI.SixShoreAtlas
abbrev Key := Fin 8
abbrev Point := Fin 6
-- Homogeneous matrices, in order, from entry six of the archived ccs1_15n.
def matrices : Array Nat := #[0x11111101111110111111011111101111110, 0x12222102222220122221022222201222210, 0x11222101222110222222011222101222110, 0x21333102333210333333021333102333210, 0x21323203123130232312032223301332210, 0x13322103322220133221033332201332210, 0x12345105432450123321054234501543210, 0x14523105432230145321054452301543210]
def cell (a : Key) (i j : Point) := (((matrices[a.val]?).getD 0) >>> (4*(6*i.val+j.val)))%16
def hard (a : Key) := a=1 ∨ a=5
instance (a : Key) : Decidable (hard a) := by unfold hard; infer_instance
/-- Exhaustive check of all regular supports and their balanced orientations.
The generator and its coverage proof do not consult the catalogue. -/
theorem checked_candidates : (SixPointSearch.generate 15 SixPointSearch.edges).all
    (SixPointSearch.checked cell) = true := by native_decide

theorem candidate_counts :
    let xs := SixPointSearch.generate 15 SixPointSearch.edges
    xs.length = 1417 ∧ (xs.filter (fun a => SixPointSearch.witness a % 2 = 0)).length = 201 := by
  native_decide

private def degreeScore (c : SixPointSearch.Table) : Nat :=
  ∑ i, ∑ j, ((∑ z : Point, if c i z = c i j then 1 else 0 : Nat)^2 +
    (if c i j = c j i then 1 else 0))

private theorem score_invariant {c b : SixPointSearch.Table} (e : Equiv.Perm Point)
    (same : ∀ i j x y, c i j = c x y ↔ b (e i) (e j) = b (e x) (e y)) :
    degreeScore c = degreeScore b := by
  have sum_eq (u v : Point → Nat) (h : ∀ i, u i = v (e i)) : ∑ i, u i = ∑ j, v j := by
    simpa only [h] using Equiv.sum_comp e v
  apply sum_eq
  intro i
  apply sum_eq
  intro j
  have inner := sum_eq (fun z => if c i z = c i j then 1 else 0)
    (fun z => if b (e i) z = b (e i) (e j) then 1 else 0) (fun z => by simp only [same])
  change (∑ z, if c i z = c i j then 1 else 0 : Nat) =
    ∑ z, if b (e i) z = b (e i) (e j) then 1 else 0 at inner
  rw [inner]
  simp only [same i j j i]

theorem distinct_models {a b : Key} (e : Equiv.Perm Point)
    (same : ∀ i j x y, cell a i j = cell a x y ↔ cell b (e i) (e j) = cell b (e x) (e y)) :
    a = b := by
  have separated : ∀ a b : Key, degreeScore (cell a) = degreeScore (cell b) → a=b := by native_decide
  exact separated a b (score_invariant e same)

/-- Check the diagonal, transpose, and all intersection numbers of every
representative. A color outside 0,...,5 has zero intersection counts. -/
theorem model_local (a : Key) : Coherent.SmallShore.Local (cell a) 0 := by
  have test : ∀ a : Key,
      (∀ i j, cell a i j < 6) ∧ (∀ i j, cell a i j=0 ↔ i=j) ∧
      (∀ i j x y, cell a i j = cell a x y → cell a j i=cell a y x) ∧
      (∀ (u v : Point) i j x y, cell a i j=cell a x y →
        SixPointSearch.steps (cell a) u.val v.val i j=SixPointSearch.steps (cell a) u.val v.val x y) := by
    native_decide
  obtain ⟨bound,diag,rev,prod⟩ := test a
  refine ⟨diag,rev,?_⟩
  intro u v i j x y eq
  by_cases hu : u<6
  · by_cases hv : v<6
    · exact prod ⟨u,hu⟩ ⟨v,hv⟩ i j x y eq
    · have absent (p q : Point) : cell a p q ≠ v := by have := bound p q; omega
      simp [absent]
  · have absent (p q : Point) : cell a p q ≠ u := by have := bound p q; omega
    simp [absent]
end QGI.SixShoreAtlas

namespace QGI.Literature
open SixShoreAtlas Coherent.SmallShore
/-- Ziv-Av, Enumeration of coherent configurations of order at most 15,
§2.1, p. 66, publishes the color-matrix list up to vertex and relation
relabeling. The eight homogeneous six-point rows are stored above.
https://actamath.savbb.sk/pdf/aumb2605.pdf -/
theorem zivAv_six_homogeneous_catalog {d : Nat} (c : Table 6) (localData : Local c d) :
    ∃ a : Key, ∃ e : Equiv.Perm Point, ∀ i j x y, c (e i) (e j)=c (e x) (e y) ↔ cell a i j=cell a x y :=
  SixPointSearch.of_checked cell checked_candidates localData
end QGI.Literature
