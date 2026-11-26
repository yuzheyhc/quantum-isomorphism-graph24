import DoubleEightFixedInterface
import FiberRectangles

namespace QGI.DoubleEight.BareLaws

open ShoreCensus (V Coloring Homogeneous side)
open FixedInterface (Compatible ConstantProduct HasIntersectionNumbers)
open Finset
open scoped BigOperators

abbrev Bare := V → V → Bool
abbrev Table := V → V → Nat

def Respects (c : Coloring) (a : Table) : Prop :=
  ∀ i j x y, c i j = c x y → a i j = a x y

def mul (a b : Table) : Table := fun i j => ∑ z, a i z * b z j

def bit (B : Bare) : Table := fun i j => if B i j then 1 else 0
def flip {α : Type} (a : V → V → α) : V → V → α := fun i j => a j i
def gram (B : Bare) : Table := mul (bit B) (flip (bit B))
def ofColor (c : Coloring) (v : Nat) : Bare := fun i j => decide (c i j = v)

def rowHistogram (a : Table) (value : Nat) (i : V) : Nat :=
  ∑ j, if a i j = value then 1 else 0

def UniformRows (a : Table) : Prop := ∀ value i j, rowHistogram a value i = rowHistogram a value j

theorem respects_map {c : Coloring} {a : Table} (h : Respects c a) (f : Nat → Nat) :
    Respects c (fun i j => f (a i j)) := fun i j x y eq => congrArg f (h i j x y eq)

theorem respects_map₂ {c : Coloring} {a b : Table} (ha : Respects c a) (hb : Respects c b)
    (f : Nat → Nat → Nat) : Respects c (fun i j => f (a i j) (b i j)) :=
  fun i j x y eq => congrArg₂ f (ha i j x y eq) (hb i j x y eq)

private def palette (c : Coloring) : Finset Nat := (univ : Finset (V × V)).image fun p => c p.1 p.2

private theorem name_mem (c : Coloring) (i j : V) : c i j ∈ palette c :=
  mem_image.mpr ⟨(i,j), mem_univ _,rfl⟩

private theorem coefficients {c : Coloring} {a : Table} (h : Respects c a) :
    ∃ f : Nat → Nat, ∀ i j, a i j = f (c i j) := by
  classical
  let f := fun t : Nat => if e : ∃ p : V × V, c p.1 p.2 = t then a e.choose.1 e.choose.2 else 0
  refine ⟨f, fun i j => ?_⟩
  have existsPair : ∃ p : V × V, c p.1 p.2 = c i j := ⟨(i,j),rfl⟩
  simp only [f, dif_pos existsPair]
  exact h i j _ _ existsPair.choose_spec.symm

private theorem expand_product (c d : Coloring) (f g : Nat → Nat) (i j : V) :
    (∑ z : V, f (c i z) * g (d z j)) =
      ∑ t ∈ palette c, ∑ u ∈ palette d,
        f t * g u * FixedInterface.product c d t u i j := by
  calc
    _ = ∑ z : V, ∑ t ∈ palette c, ∑ u ∈ palette d,
        (if c i z = t ∧ d z j = u then f t * g u else 0) := by
      apply sum_congr rfl
      intro z _
      simp [ite_and, Finset.sum_ite_eq, name_mem, Finset.sum_ite_irrel]
    _ = _ := by
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro t _
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro u _
      simp only [FixedInterface.product, List.sum_ofFn, Finset.mul_sum, mul_ite, mul_one, mul_zero]

/-- A multiplication-closed color law for basic relations is automatically
closed for every pair of tables constant on the two input colorings. -/
theorem respects_mul {c d out : Coloring} {a b : Table} (closure : ConstantProduct c d out)
    (ha : Respects c a) (hb : Respects d b) : Respects out (mul a b) := by
  obtain ⟨f,hf⟩ := coefficients ha
  obtain ⟨g,hg⟩ := coefficients hb
  intro i j x y eq
  simp only [mul,hf,hg,expand_product]
  exact sum_congr rfl fun t _ => sum_congr rfl fun u _ => by rw [closure t u i j x y eq]

private theorem local_product {c : Coloring} (hc : Homogeneous c) : ConstantProduct c c c := by
  intro t u i j x y eq
  simpa only [FixedInterface.product, List.sum_ofFn, ShoreCensus.intersection]
    using hc.products i j x y eq t u

theorem respects_local_mul {c : Coloring} {a b : Table} (hc : Homogeneous c)
    (ha : Respects c a) (hb : Respects c b) : Respects c (mul a b) :=
  respects_mul (local_product hc) ha hb

/-- The row histogram of *any* color-constant table is independent of the
point: an indicator of one entry value times the all-ones matrix has constant diagonal. -/
theorem uniform_of_respects {c : Coloring} {a : Table} (hc : Homogeneous c)
    (ha : Respects c a) : UniformRows a := by
  intro v i j
  let f := fun k : Nat => if k = v then 1 else 0
  have ones : Respects c (fun _ _ => 1) := fun _ _ _ _ _ => rfl
  have uniform := respects_local_mul hc (respects_map ha f) ones
  have eq := ((hc.diagonal i i).mpr rfl).trans ((hc.diagonal j j).mpr rfl).symm
  simpa [mul, f, rowHistogram] using uniform i i j j eq

theorem respects_gram {c a : Coloring} (compat : Compatible c a) (v : Nat) :
    Respects a (gram (ofColor c v)) := by
  have entries (i j : V) : gram (ofColor c v) i j =
      FixedInterface.product c (FixedInterface.transpose c) v v i j := by
    simp only [gram, mul, bit, flip, ofColor, decide_eq_true_eq, FixedInterface.product,
      FixedInterface.transpose, List.sum_ofFn]
    apply sum_congr rfl
    intro z _
    split_ifs <;> simp_all
  intro i j x y eq
  simpa only [entries] using compat.1 v v i j x y eq

theorem uniform_gram {c a : Coloring} (hc : Homogeneous a) (compat : Compatible c a)
    (v : Nat) : UniformRows (gram (ofColor c v)) :=
  uniform_of_respects hc (respects_gram compat v)

private theorem constant_degree {c a : Coloring} (hc : Homogeneous a) (compat : Compatible c a)
    (v : Nat) (i j : V) :
    FiberRectangles.degree (ofColor c v i) = FiberRectangles.degree (ofColor c v j) := by
  have eq := ((hc.diagonal i i).mpr rfl).trans ((hc.diagonal j j).mpr rfl).symm
  have diag (i : V) : gram (ofColor c v) i i = FiberRectangles.degree (ofColor c v i) := by
    have h (k : V) : bit (ofColor c v) i k * bit (ofColor c v) i k =
        (if c i k = v then 1 else 0) := by by_cases e : c i k = v <;> simp [bit, ofColor, e]
    simp [gram, mul, flip, h, ofColor, FiberRectangles.degree]
  simpa only [diag] using respects_gram compat v i i j j eq

/-- Every cross color has constant row and column degrees, including absent colors. -/
theorem biregular {c l r : Coloring} (hl : Homogeneous l) (hr : Homogeneous r)
    (lc : Compatible c l) (rc : Compatible (FixedInterface.transpose c) r) :
    FiberRectangles.BiregularColors c := by
  intro v
  exact ⟨_, _, fun i => constant_degree hl lc v i 0, fun j => constant_degree hr rc v j 0⟩

def level (a : Table) (v : Nat) : Table := fun i j => if a i j = v then 1 else 0

def OnSupport (B : Bare) (a : Table) : Prop :=
  ∀ i j x y, B i j = true → B x y = true → a i j = a x y

/-- Necessary histogram and support tests in one orientation, at every valency. -/
structure OneSide (B : Bare) : Prop where
  gram_rows : UniformRows (gram B)
  gram_square_rows : UniformRows (mul (gram B) (gram B))
  supported : OnSupport B (mul (level (gram B) 1) (bit B))

def Necessary (B : Bare) : Prop := OneSide B ∧ OneSide (flip B)

theorem oneSide {c a : Coloring} (ha : Homogeneous a) (h : Compatible c a) (v : Nat) :
    OneSide (ofColor c v) := by
  have g := respects_gram h v
  have lev := respects_map g (fun n => if n = 1 then 1 else 0)
  have b : Respects c (bit (ofColor c v)) := by
    intro i j x y eq
    simp only [bit, ofColor, eq]
  have prod := respects_mul h.2 lev b
  refine ⟨uniform_of_respects ha g, uniform_of_respects ha (respects_local_mul ha g g), ?_⟩
  intro i j x y e e'
  exact prod i j x y ((of_decide_eq_true e).trans (of_decide_eq_true e').symm)

theorem necessary {c l r : Coloring} (hl : Homogeneous l) (hr : Homogeneous r)
    (lc : Compatible c l) (rc : Compatible (FixedInterface.transpose c) r) (v : Nat) :
    Necessary (ofColor c v) := ⟨oneSide hl lc v, oneSide hr rc v⟩

/-- All four scalar-color laws are available for raw configurations in arbitrary palettes. -/
theorem raw_compatible (m : V ⊕ V → V ⊕ V → Nat)
    (rectangle : ∀ i j x y, m i j = m x y → (side i, side j) = (side x, side y))
    (rev : ∀ i j x y, m i j = m x y → m j i = m y x) (products : HasIntersectionNumbers m) :
    let c : Coloring := fun i j => m (.inl i) (.inr j)
    let l : Coloring := fun i j => m (.inl i) (.inl j)
    let r : Coloring := fun i j => m (.inr i) (.inr j)
    Compatible c l ∧ Compatible (FixedInterface.transpose c) r := by
  dsimp only
  apply FixedInterface.compatibility_of_products
  apply FixedInterface.rename_products (m := m) _ products
  rintro (i|i) (j|j) (x|x) (y|y) <;> simp [FixedInterface.completion]
    <;> first | exact ⟨rev _ _ _ _, rev _ _ _ _⟩
              | intro h; have e := rectangle _ _ _ _ h; simp [side] at e

/-- Unnormalized, unrestricted palettes and arbitrary point order: every raw
cross color is biregular and passes all histogram/support pruning conditions. -/
theorem raw_necessary (m : V ⊕ V → V ⊕ V → Nat)
    (hl : Homogeneous (fun i j => m (.inl i) (.inl j)))
    (hr : Homogeneous (fun i j => m (.inr i) (.inr j)))
    (rectangle : ∀ i j x y, m i j = m x y → (side i, side j) = (side x, side y))
    (rev : ∀ i j x y, m i j = m x y → m j i = m y x) (products : HasIntersectionNumbers m) :
    let c : Coloring := fun i j => m (.inl i) (.inr j)
    FiberRectangles.BiregularColors c ∧ ∀ v, Necessary (ofColor c v) := by
  obtain ⟨lc,rc⟩ := raw_compatible m rectangle rev products
  exact ⟨biregular hl hr lc rc, necessary hl hr lc rc⟩

end QGI.DoubleEight.BareLaws
