import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Bilinear
import Mathlib.Data.Matrix.Hadamard
import Mathlib.LinearAlgebra.Span.Basic

namespace QGI.DoubleEightDecorations
open Matrix
open scoped Matrix

variable {R X Y : Type*} [CommSemiring R] [Fintype X] [Fintype Y]

/-- The internal relation span of one shore, closed under the two operations
needed in the ordinary matrix-product test. An internal color scheme supplies
these laws before it is attached to the other shore. -/
structure Shore (R X : Type*) [CommSemiring R] [Fintype X] where
  space : Submodule R (Matrix X X R)
  mul_mem : ∀ {a b}, a ∈ space → b ∈ space → a * b ∈ space
  transpose_mem : ∀ {a}, a ∈ space → aᵀ ∈ space

variable (C : Submodule R (Matrix X Y R)) (L : Shore R X) (T : Shore R Y)

/-- A lower-left block is allowed precisely when its transpose belongs to
the fixed upper-right space C. -/
def Allowed (M : Matrix (X ⊕ Y) (X ⊕ Y) R) : Prop :=
  M.toBlocks₁₁ ∈ L.space ∧ M.toBlocks₁₂ ∈ C ∧ M.toBlocks₂₁ᵀ ∈ C ∧ M.toBlocks₂₂ ∈ T.space

def decorationSpace : Submodule R (Matrix (X ⊕ Y) (X ⊕ Y) R) where
  carrier := {M | Allowed C L T M}
  zero_mem' := ⟨L.space.zero_mem, C.zero_mem, C.zero_mem, T.space.zero_mem⟩
  add_mem' h k := ⟨L.space.add_mem h.1 k.1, C.add_mem h.2.1 k.2.1,
    C.add_mem h.2.2.1 k.2.2.1, T.space.add_mem h.2.2.2 k.2.2.2⟩
  smul_mem' s _ h := ⟨L.space.smul_mem s h.1, C.smul_mem s h.2.1,
    C.smul_mem s h.2.2.1, T.space.smul_mem s h.2.2.2⟩

def ProductClosed : Prop :=
  ∀ {M N}, Allowed C L T M → Allowed C L T N → Allowed C L T (M * N)

def LeftCompatible : Prop :=
  (∀ a ∈ L.space, ∀ c ∈ C, a * c ∈ C) ∧
    ∀ c ∈ C, ∀ d ∈ C, c * dᵀ ∈ L.space

def RightCompatible : Prop :=
  (∀ c ∈ C, ∀ b ∈ T.space, c * b ∈ C) ∧
    ∀ c ∈ C, ∀ d ∈ C, cᵀ * d ∈ T.space

private theorem assemble {a b c d} (ha : a ∈ L.space) (hc : c ∈ C) (hd : d ∈ C)
    (hb : b ∈ T.space) : Allowed C L T (fromBlocks a c dᵀ b) :=
  ⟨ha, hc, by simpa using hd, hb⟩

/-- Transposition exchanges the two rectangular blocks, with no further
compatibility equation between the two choices of shore. -/
theorem transpose_allowed {M} (hm : Allowed C L T M) : Allowed C L T Mᵀ :=
  ⟨L.transpose_mem hm.1, hm.2.2.1, hm.2.1, T.transpose_mem hm.2.2.2⟩

/-- Ordinary multiplication of full block matrices is closed exactly when
the two shores separately pass their cross-action and Gram-product tests. -/
theorem productClosed_iff :
    ProductClosed C L T ↔ LeftCompatible C L ∧ RightCompatible C T := by
  constructor
  · intro closed
    constructor
    · constructor
      · intro a ha c hc
        have h := (closed
          (assemble C L T ha C.zero_mem C.zero_mem T.space.zero_mem)
          (assemble C L T L.space.zero_mem hc C.zero_mem T.space.zero_mem)).2.1
        simpa [fromBlocks_multiply] using h
      · intro c hc d hd
        have h := (closed
          (assemble C L T L.space.zero_mem hc C.zero_mem T.space.zero_mem)
          (assemble C L T L.space.zero_mem C.zero_mem hd T.space.zero_mem)).1
        simpa [fromBlocks_multiply] using h
    · constructor
      · intro c hc b hb
        have h := (closed
          (assemble C L T L.space.zero_mem hc C.zero_mem T.space.zero_mem)
          (assemble C L T L.space.zero_mem C.zero_mem C.zero_mem hb)).2.1
        simpa [fromBlocks_multiply] using h
      · intro c hc d hd
        have h := (closed
          (assemble C L T L.space.zero_mem C.zero_mem hc T.space.zero_mem)
          (assemble C L T L.space.zero_mem hd C.zero_mem T.space.zero_mem)).2.2.2
        simpa [fromBlocks_multiply] using h
  · rintro ⟨left, right⟩ M N hm hn
    rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, fromBlocks_multiply]
    refine ⟨L.space.add_mem (L.mul_mem hm.1 hn.1) ?_,
      C.add_mem (left.1 _ hm.1 _ hn.2.1) (right.1 _ hm.2.1 _ hn.2.2.2), ?_,
      T.space.add_mem ?_ (T.mul_mem hm.2.2.2 hn.2.2.2)⟩
    · simpa only [transpose_transpose] using left.2 _ hm.2.1 _ hn.2.2.1
    · simp only [toBlocks_fromBlocks₂₁, transpose_add, transpose_mul]
      exact C.add_mem (left.1 _ (L.transpose_mem hn.1) _ hm.2.2.1)
        (right.1 _ hn.2.2.1 _ (T.transpose_mem hm.2.2.2))
    · simpa only [transpose_transpose] using right.2 _ hm.2.2.1 _ hn.2.1

/-- With the rectangular color space fixed, the set of legal decorations
is the Cartesian product of the left choices and the right choices. -/
theorem decoration_product :
    {p : Shore R X × Shore R Y | ProductClosed C p.1 p.2} =
      Set.prod {l | LeftCompatible C l} {r | RightCompatible C r} := by
  ext p
  exact productClosed_iff C p.1 p.2

/-- The span of the supplied, individually named relation matrices. -/
def relationSpan {I A B : Type*} (v : I → Matrix A B R) : Submodule R (Matrix A B R) :=
  Submodule.span R (Set.range v)

section Bilinear
variable {M N P I J : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P]

private theorem span_maps_to (a : I → M) (f : M →ₗ[R] P) (D : Submodule R P)
    (test : ∀ i, f (a i) ∈ D) {x} (hx : x ∈ Submodule.span R (Set.range a)) : f x ∈ D := by
  have inclusion : Submodule.span R (Set.range a) ≤ D.comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact test i
  exact inclusion hx

private theorem bilinear_test (a : I → M) (b : J → N) (D : Submodule R P)
    (f : M →ₗ[R] N →ₗ[R] P) :
    (∀ x ∈ Submodule.span R (Set.range a), ∀ y ∈ Submodule.span R (Set.range b), f x y ∈ D) ↔
      ∀ i j, f (a i) (b j) ∈ D := by
  constructor
  · intro h i j
    exact h _ (Submodule.subset_span ⟨i,rfl⟩) _ (Submodule.subset_span ⟨j,rfl⟩)
  · intro test x hx y hy
    exact span_maps_to b (f x) D
      (fun j => span_maps_to a (f.flip (b j)) D (fun i => test i j) hx) hy
end Bilinear

/-- For matrix spans generated by named colors l, c, r, it suffices to check
four families on the colors. The first two tests mention only the left
decoration and c; the last two mention only the right decoration and c. -/
theorem closure_iff_generator_tests {I J K : Type*}
    (l : I → Matrix X X R) (c : J → Matrix X Y R) (r : K → Matrix Y Y R)
    (hl : L.space = relationSpan l) (hr : T.space = relationSpan r) :
    ProductClosed (relationSpan c) L T ↔
      ((∀ i j, l i * c j ∈ relationSpan c) ∧
       (∀ i j, c i * (c j)ᵀ ∈ L.space)) ∧
      ((∀ i j, c i * r j ∈ relationSpan c) ∧
       (∀ i j, (c i)ᵀ * c j ∈ T.space)) := by
  rw [productClosed_iff]
  unfold LeftCompatible RightCompatible
  rw [hl, hr]
  let tr := (transposeLinearEquiv X Y R R).toLinearMap
  let leftGram : Matrix X Y R →ₗ[R] Matrix X Y R →ₗ[R] Matrix X X R :=
    (mulLinearMap R).compl₂ tr
  let rightGram : Matrix X Y R →ₗ[R] Matrix X Y R →ₗ[R] Matrix Y Y R :=
    (mulLinearMap R).comp tr
  exact and_congr
    (and_congr (bilinear_test l c _ (mulLinearMap R)) (bilinear_test c c _ leftGram))
    (and_congr (bilinear_test c r _ (mulLinearMap R)) (bilinear_test c c _ rightGram))

section Colors

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The zero-one incidence matrix of one named color of the cross rectangle. -/
def indicator (color : X → Y → I) (i : I) : Matrix X Y R :=
  fun x y => if color x y = i then 1 else 0

omit [Fintype X] [Fintype Y] in
theorem mem_color_span (color : X → Y → I) (M : Matrix X Y R) :
    M ∈ relationSpan (indicator (R := R) color) ↔
      ∃ w : I → R, ∀ x y, M x y = w (color x y) := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨i,rfl⟩ := h
      exact ⟨fun j => if j = i then 1 else 0, fun _ _ => rfl⟩
    | zero => exact ⟨fun _ => 0, fun _ _ => rfl⟩
    | add a b _ _ ha hb =>
      obtain ⟨u, hu⟩ := ha
      obtain ⟨v, hv⟩ := hb
      exact ⟨fun i => u i + v i, fun x y => by simp [Matrix.add_apply, hu, hv]⟩
    | smul s a _ ha =>
      obtain ⟨u, hu⟩ := ha
      exact ⟨fun i => s * u i, fun x y => by simp [Matrix.smul_apply, hu, smul_eq_mul]⟩
  · rintro ⟨w, h⟩
    have e : M = ∑ i, w i • indicator color i := by
      ext x y
      simp [Matrix.sum_apply, Matrix.smul_apply, indicator, smul_eq_mul, mul_ite, h]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

def allOnes (R X Y : Type*) [One R] : Matrix X Y R := fun _ _ => 1

omit [Fintype X] [Fintype Y] in
private theorem colors_schur (color : X → Y → I) {A B : Matrix X Y R}
    (ha : A ∈ relationSpan (indicator color)) (hb : B ∈ relationSpan (indicator color)) :
    A.hadamard B ∈ relationSpan (indicator color) := by
  obtain ⟨u, hu⟩ := (mem_color_span color _).mp ha
  obtain ⟨v, hv⟩ := (mem_color_span color _).mp hb
  exact (mem_color_span color _).mpr ⟨fun i => u i * v i, fun x y => by
    rw [hadamard_apply, hu, hv]⟩

variable [DecidableEq X] [DecidableEq Y]

/-- The internal scheme already contains both canonical matrices and is
closed under the entrywise product. -/
def LocalLaws (A : Shore R X) : Prop :=
  (1 : Matrix X X R) ∈ A.space ∧ allOnes R X X ∈ A.space ∧
    ∀ a ∈ A.space, ∀ b ∈ A.space, Matrix.hadamard a b ∈ A.space

/-- The full relation space contains I and J, and is closed under ordinary
multiplication, entrywise multiplication and transpose. -/
def CoherentBlocks : Prop :=
  ProductClosed C L T ∧ Allowed C L T 1 ∧ Allowed C L T (allOnes R _ _) ∧
    (∀ {a}, Allowed C L T a → Allowed C L T aᵀ) ∧
    ∀ {a b}, Allowed C L T a → Allowed C L T b → Allowed C L T (a.hadamard b)

theorem coherentBlocks_iff (color : X → Y → I) (hl : LocalLaws L) (hr : LocalLaws T) :
    CoherentBlocks (relationSpan (indicator color)) L T ↔
      LeftCompatible (relationSpan (indicator color)) L ∧
        RightCompatible (relationSpan (indicator color)) T := by
  let S := relationSpan (indicator (R := R) color)
  constructor
  · exact fun h => (productClosed_iff S L T).mp h.1
  · intro h
    have ones : allOnes R X Y ∈ S :=
      (mem_color_span color _).mpr ⟨fun _ => 1, fun _ _ => rfl⟩
    refine ⟨(productClosed_iff S L T).mpr h, ?_, ⟨hl.2.1, ones, ones, hr.2.1⟩,
      transpose_allowed S L T, ?_⟩
    · rw [← @fromBlocks_one X Y R]
      exact assemble S L T hl.1 S.zero_mem S.zero_mem hr.1
    · intro a b ha hb
      exact ⟨hl.2.2 _ ha.1 _ hb.1, colors_schur color ha.2.1 hb.2.1,
        colors_schur color ha.2.2.1 hb.2.2.1, hr.2.2 _ ha.2.2.2 _ hb.2.2.2⟩

/-- With a fixed cross-color partition, the coherent decorations by valid
local schemes form exactly the product of the two separate sets of choices. -/
theorem coherent_decoration_product (color : X → Y → I) :
    {p : Shore R X × Shore R Y | LocalLaws p.1 ∧ LocalLaws p.2 ∧
      CoherentBlocks (relationSpan (indicator color)) p.1 p.2} =
    Set.prod {l | LocalLaws l ∧ LeftCompatible (relationSpan (indicator color)) l}
      {r | LocalLaws r ∧ RightCompatible (relationSpan (indicator color)) r} := by
  ext p
  constructor
  · rintro ⟨hl,hr,h⟩
    obtain ⟨l,r⟩ := (coherentBlocks_iff p.1 p.2 color hl hr).mp h
    exact ⟨⟨hl,l⟩, hr, r⟩
  · rintro ⟨⟨hl,l⟩,hr,r⟩
    exact ⟨hl,hr,(coherentBlocks_iff p.1 p.2 color hl hr).mpr ⟨l,r⟩⟩

end Colors

end QGI.DoubleEightDecorations
