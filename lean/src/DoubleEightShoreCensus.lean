import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import DoubleEightUniform
import RowCensusSound
import data.RowCensus8

namespace QGI.DoubleEight.ShoreCensus

open scoped BigOperators

abbrev V := Fin 8
abbrev Coloring := V → V → Nat

def intersection (c : Coloring) (a b : Nat) (i j : V) : Nat :=
  ∑ k : V, if c i k = a ∧ c k j = b then 1 else 0

/-- A directed homogeneous coherent configuration. The used numeric colors
are its nonempty basic relations; unused names do not affect the partition. -/
structure Homogeneous (c : Coloring) : Prop where
  diagonal : ∀ i j, c i j = c 0 0 ↔ i = j
  transpose : ∀ i j k l, c i j = c k l → c j i = c l k
  products : ∀ i j k l, c i j = c k l → ∀ a b : Nat,
    intersection c a b i j = intersection c a b k l

abbrev Scheme := {c : Coloring // Homogeneous c}

/-- A point permutation induces a bijection between the actual color
classes, whose names may be unrelated. -/
def Isomorphic (c d : Coloring) : Prop :=
  ∃ e : V ≃ V, ∀ i j k l, c i j = c k l ↔ d (e i) (e j) = d (e k) (e l)

def pointSetoid : Setoid Scheme where
  r c d := Isomorphic c.val d.val
  iseqv := {
    refl := fun _ => ⟨Equiv.refl _, fun _ _ _ _ => Iff.rfl⟩
    symm := by
      rintro _ _ ⟨e, he⟩
      refine ⟨e.symm, fun i j k l => ?_⟩
      simpa using (he (e.symm i) (e.symm j) (e.symm k) (e.symm l)).symm
    trans := by
      rintro _ _ _ ⟨e, he⟩ ⟨f, hf⟩
      exact ⟨e.trans f, fun i j k l =>
        (he i j k l).trans (hf (e i) (e j) (e k) (e l))⟩ }

abbrev Classes := Quotient pointSetoid

def seed (a : Fin 21) : Coloring := fun i j =>
  (UniformInput.shores.getD a.val #[]).getD (8 * i.val + j.val) 0

private def Checked (c : Coloring) : Prop :=
  (∀ i j, c i j < 8) ∧
  (∀ i j, c i j = c 0 0 ↔ i = j) ∧
  (∀ i j k l, c i j = c k l → c j i = c l k) ∧
  (∀ i j k l, c i j = c k l → ∀ a b : V,
    intersection c a.val b.val i j = intersection c a.val b.val k l)

private instance (c : Coloring) : Decidable (Checked c) := by unfold Checked; infer_instance

private theorem checked_seeds : ∀ a : Fin 21, Checked (seed a) := by native_decide

theorem seed_homogeneous (a : Fin 21) : Homogeneous (seed a) := by
  obtain ⟨bound, diagonal, transpose, products⟩ := checked_seeds a
  refine ⟨diagonal, transpose, ?_⟩
  intro i j k l same u v
  by_cases hu : u < 8
  · by_cases hv : v < 8
    · exact products i j k l same ⟨u, hu⟩ ⟨v, hv⟩
    · have h (x y : V) : seed a x y ≠ v :=
        Nat.ne_of_lt (lt_of_lt_of_le (bound x y) (Nat.le_of_not_lt hv))
      simp [intersection, h]
  · have h (x y : V) : seed a x y ≠ u :=
      Nat.ne_of_lt (lt_of_lt_of_le (bound x y) (Nat.le_of_not_lt hu))
    simp [intersection, h]

private def edgeOf (c : Coloring) (i j u v : V) : Nat :=
  if c i j = c u v then 1 else 0

private def two (c : Coloring) (i j x y : V) : Nat :=
  ∑ z : V, edgeOf c i j x z * edgeOf c i j z y

/-- For every based edge-color, square the outgoing valency and each of the
rooted monochromatic closed walk counts of lengths two and four, then sum. -/
def fingerprint (c : Coloring) : Nat :=
  ∑ i : V, ∑ j : V, ((∑ z : V, edgeOf c i j i z) ^ 2 +
    (two c i j i i) ^ 2 + (∑ z : V, two c i j i z * two c i j z i) ^ 2)

private theorem reindex_sum (e : V ≃ V) (f g : V → Nat) (h : ∀ i, f i = g (e i)) :
    (∑ i, f i) = ∑ j, g j := by
  simpa only [h] using e.sum_comp g

theorem fingerprint_eq {c d : Coloring} (h : Isomorphic c d) :
    fingerprint c = fingerprint d := by
  obtain ⟨e, he⟩ := h
  have edge (i j u v : V) : edgeOf c i j u v = edgeOf d (e i) (e j) (e u) (e v) := by
    simp only [edgeOf, he i j u v]
  have paths (i j u v : V) : two c i j u v = two d (e i) (e j) (e u) (e v) := by
    unfold two
    apply reindex_sum e
    intro z
    simp only [edge]
  unfold fingerprint
  apply reindex_sum e
  intro i
  apply reindex_sum e
  intro j
  have deg := reindex_sum e _ _ (fun z => edge i j i z)
  have four := reindex_sum e (fun z => two c i j i z * two c i j z i)
    (fun z => two d (e i) (e j) (e i) z * two d (e i) (e j) z (e i))
    (fun z => congrArg₂ (· * ·) (paths i j i z) (paths i j z i))
  rw [deg, paths i j i i, four]

private theorem distinct_scores : ∀ a b : Fin 21,
    fingerprint (seed a) = fingerprint (seed b) → a = b := by native_decide

theorem seed_injective {a b : Fin 21} (h : Isomorphic (seed a) (seed b)) : a = b :=
  distinct_scores a b (fingerprint_eq h)

private def seedClass (a : Fin 21) : Classes := Quotient.mk pointSetoid ⟨seed a, seed_homogeneous a⟩

private def certificates := RowCensus.decode RowCensus.raw8

set_option maxRecDepth 100000 in
private theorem verified_certificates : ∀ i : Fin certificates.size,
    RowCensus.verified seed certificates i.val=true := by native_decide

/-- Completeness of the 21 matrices, including directed and thin cases.
The row-extension theorem reconstructs an isomorphism for every input. -/
theorem every_shore (c : Coloring) (hc : Homogeneous c) :
    ∃ a : Fin 21, Isomorphic (seed a) c :=
  RowCensus.census_complete seed certificates (by native_decide) (by native_decide)
    verified_certificates c (RowCensus.of_intersections c hc.diagonal hc.transpose
      (fun a b i j x y eq => hc.products i j x y eq a b))

/-- The order-eight entry of Cameron's Table 1 follows from the checked matrices. -/
theorem cameron_order_eight_class_count : Nat.card Classes = 21 := by
  have inj : Function.Injective seedClass := fun _ _ h => seed_injective (Quotient.exact h)
  have sur : Function.Surjective seedClass := by
    intro q
    induction q using Quotient.inductionOn with
    | _ obj =>
      obtain ⟨i,iso⟩ := every_shore obj.val obj.property
      exact ⟨i,Quotient.sound iso⟩
  simpa using Nat.card_congr (Equiv.ofBijective seedClass ⟨inj,sur⟩).symm

/-- Numeric color names that occur on at least one ordered pair. -/
def Palette (c : Coloring) := Set.range (fun ij : V × V => c ij.1 ij.2)

def name (c : Coloring) (i j : V) : Palette c := ⟨c i j, ⟨(i, j), rfl⟩⟩

/-- Unpack a partition isomorphism as simultaneous point and color bijections. -/
theorem point_and_color {c d : Coloring} (h : Isomorphic c d) :
    ∃ (e : V ≃ V) (f : Palette c ≃ Palette d), ∀ i j, f (name c i j) = name d (e i) (e j) := by
  classical
  obtain ⟨e, he⟩ := h
  let pick (u : Palette c) : V × V := Classical.choose u.property
  have hp (u : Palette c) : c (pick u).1 (pick u).2 = u.val := Classical.choose_spec u.property
  let rename (u : Palette c) : Palette d := name d (e (pick u).1) (e (pick u).2)
  have acts (i j : V) : rename (name c i j) = name d (e i) (e j) :=
    Subtype.ext ((he _ _ i j).mp (hp (name c i j)))
  have inj : Function.Injective rename := by
    intro u v h
    exact Subtype.ext ((hp u).symm.trans (((he _ _ _ _).mpr (congrArg Subtype.val h)).trans (hp v)))
  have sur : Function.Surjective rename := by
    rintro ⟨_, ⟨⟨i, j⟩, rfl⟩⟩
    refine ⟨name c (e.symm i) (e.symm j), ?_⟩
    simpa using acts (e.symm i) (e.symm j)
  exact ⟨e, Equiv.ofBijective rename ⟨inj, sur⟩, acts⟩

theorem every_shore_labelled (c : Coloring) (hc : Homogeneous c) :
    ∃ (a : Fin 21) (e : V ≃ V) (f : Palette (seed a) ≃ Palette c),
      ∀ i j, f (name (seed a) i j) = name c (e i) (e j) := by
  obtain ⟨a, ha⟩ := every_shore c hc
  exact ⟨a, point_and_color ha⟩

abbrev UniformColor := (Nat ⊕ Nat) ⊕ Bool

/-- The uniform two-shore completion, keeping each shore's relation names
distinct from the other's and reserving one color for each cross direction. -/
def completion (c d : Coloring) : V ⊕ V → V ⊕ V → UniformColor
  | .inl i, .inl j => .inl (.inl (c i j))
  | .inr i, .inr j => .inl (.inr (d i j))
  | .inl _, .inr _ => .inr false
  | .inr _, .inl _ => .inr true

def PartitionIso {X Y A B : Type} (c : X → X → A) (d : Y → Y → B) : Prop :=
  ∃ e : X ≃ Y, ∀ i j k l, c i j = c k l ↔ d (e i) (e j) = d (e k) (e l)

private theorem isoTrans {X Y Z A B C : Type} {c : X → X → A} {d : Y → Y → B}
    {f : Z → Z → C} (h : PartitionIso c d) (g : PartitionIso d f) : PartitionIso c f := by
  obtain ⟨e, he⟩ := h
  obtain ⟨p, hp⟩ := g
  exact ⟨e.trans p, fun i j k l => (he i j k l).trans (hp (e i) (e j) (e k) (e l))⟩

private theorem isoSymm {X Y A B : Type} {c : X → X → A} {d : Y → Y → B}
    (h : PartitionIso c d) : PartitionIso d c := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun i j k l => ?_⟩
  simpa using (he (e.symm i) (e.symm j) (e.symm k) (e.symm l)).symm

private theorem completion_iso {a b c d : Coloring} (ha : Isomorphic a c)
    (hb : Isomorphic b d) : PartitionIso (completion a b) (completion c d) := by
  obtain ⟨e, he⟩ := ha
  obtain ⟨f, hf⟩ := hb
  refine ⟨e.sumCongr f, ?_⟩
  rintro (i | i) (j | j) (k | k) (l | l) <;> simp [completion, he, hf]

private theorem swap_iso (c d : Coloring) : PartitionIso (completion c d) (completion d c) := by
  refine ⟨Equiv.sumComm _ _, ?_⟩
  rintro (i | i) (j | j) (k | k) (l | l) <;> simp [completion]

private def encode : UniformColor → Nat
  | .inl (.inl x) => 2 + 2 * x
  | .inl (.inr y) => 3 + 2 * y
  | .inr false => 0
  | .inr true => 1

private theorem encode_injective : Function.Injective encode := by
  rintro ((x | x) | (_ | _)) ((y | y) | (_ | _)) h <;> simp_all [encode] <;> omega

private theorem model_coordinates : ∀ (a b : Fin 21) (i j : V ⊕ V),
    encode (completion (seed a) (seed b) i j) =
      Uniform.model a b (finSumFinEquiv i) (finSumFinEquiv j) := by native_decide

attribute [local irreducible] Uniform.witness Uniform.rows Uniform.model seed

private theorem sorted_row (a b : Fin 21) (hab : a ≤ b) :
    ∃ r : Fin 636, Uniform.isUniform (Uniform.rows.getD r.val #[]) = true ∧
      PartitionIso (completion (seed a) (seed b)) (Uniform.color (Uniform.rows.getD r.val #[])) := by
  obtain ⟨bound, e, he⟩ := Uniform.realizes_pair a b hab
  have size : Uniform.rows.size = 636 := Uniform.catalogue_counts.2.2.1
  let r : Fin 636 := ⟨(Uniform.witness a b).row,
    calc (Uniform.witness a b).row < Uniform.rows.size := bound
         _ = 636 := size⟩
  have rowId : (Uniform.witness a b).row = r.val := rfl
  have uniform := (Uniform.uniform_iff_pair r).2 ⟨a, b, hab, rowId⟩
  refine ⟨r, uniform, finSumFinEquiv.trans e, ?_⟩
  intro i j k l
  exact encode_injective.eq_iff.symm.trans
    ((by rw [model_coordinates a b i j, model_coordinates a b k l] :
       encode (completion (seed a) (seed b) i j) = encode (completion (seed a) (seed b) k l) ↔
       Uniform.model a b (finSumFinEquiv i) (finSumFinEquiv j) =
       Uniform.model a b (finSumFinEquiv k) (finSumFinEquiv l)).trans
      (he (finSumFinEquiv i) (finSumFinEquiv j) (finSumFinEquiv k) (finSumFinEquiv l)))

/-- Uniform completions of arbitrary pairs of eight-point homogeneous schemes
are covered by the actual uniform rows of the 636-entry catalogue. -/
theorem every_uniform_completion (c d : Coloring) (hc : Homogeneous c) (hd : Homogeneous d) :
    ∃ r : Fin 636, Uniform.isUniform (Uniform.rows.getD r.val #[]) = true ∧
      PartitionIso (completion c d) (Uniform.color (Uniform.rows.getD r.val #[])) := by
  obtain ⟨a, ha⟩ := every_shore c hc
  obtain ⟨b, hb⟩ := every_shore d hd
  rcases le_total a b with h | h
  · obtain ⟨r, hr, iso⟩ := sorted_row a b h
    exact ⟨r, hr, isoTrans (isoSymm (completion_iso ha hb)) iso⟩
  · obtain ⟨r, hr, iso⟩ := sorted_row b a h
    exact ⟨r, hr, isoTrans (swap_iso c d) (isoTrans (isoSymm (completion_iso hb ha)) iso)⟩

def side : V ⊕ V → Bool
  | .inl _ => false
  | .inr _ => true

/-- Direct raw-color version. Each color lies in one source/target fiber
rectangle. Both cross rectangles are monochromatic, and the two diagonal
restrictions are homogeneous. No particular global color numbering is needed. -/
theorem every_uniform_two_fiber (m : V ⊕ V → V ⊕ V → Nat)
    (hl : Homogeneous (fun i j => m (.inl i) (.inl j)))
    (hr : Homogeneous (fun i j => m (.inr i) (.inr j)))
    (rectangle : ∀ i j k l, m i j = m k l → (side i, side j) = (side k, side l))
    (forward : ∀ i j k l : V, m (.inl i) (.inr j) = m (.inl k) (.inr l))
    (backward : ∀ i j k l : V, m (.inr i) (.inl j) = m (.inr k) (.inl l)) :
    ∃ r : Fin 636, Uniform.isUniform (Uniform.rows.getD r.val #[]) = true ∧
      PartitionIso m (Uniform.color (Uniform.rows.getD r.val #[])) := by
  obtain ⟨r, h, realized⟩ := every_uniform_completion _ _ hl hr
  refine ⟨r, h, isoTrans ?_ realized⟩
  refine ⟨Equiv.refl _, ?_⟩
  rintro (i | i) (j | j) (k | k) (l | l) <;> simp [completion]
    <;> first | exact forward _ _ _ _ | exact backward _ _ _ _
              | intro same; have hside := rectangle _ _ _ _ same; simp [side] at hside

end QGI.DoubleEight.ShoreCensus
