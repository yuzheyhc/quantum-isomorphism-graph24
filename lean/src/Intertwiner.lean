import Synchrony

open scoped BigOperators

/-!
A numerical (complex) matrix criterion on the algebraic cyclic space of an
arbitrary perfect commuting strategy. The field is used only when a nonzero
difference of scalar entries is cancelled. No planarity assumption occurs.
-/
noncomputable section
namespace QGI.Intertwiner
open QGI.Synchrony

variable {n : Nat} {G H : Graph n} {K : Type}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable (p : PerfectStrategy G H K)

abbrev Mat (n : Nat) := Matrix (Fin n) (Fin n) ℂ
abbrev U (x a : Fin n) := restricted p (false,x) a

/-- A U = U B as a vector identity on the cyclic subspace. -/
def Intertwines (A B : Mat n) : Prop :=
  ∀ x b (v : cyclic p),
    (∑ y, A x y • U p y b v) = ∑ a, B a b • U p x a v

/-- Every mismatch of scalar entries forces the ordered product to vanish. -/
def Compatible (A B : Mat n) : Prop :=
  ∀ x y a b, A x y ≠ B a b →
    (U p x a).comp (U p y b) = 0

private theorem eval_zero {L R : (cyclic p) →ₗ[ℂ] (cyclic p)}
    (h : L.comp R = 0) (v : cyclic p) : L (R v) = 0 :=
  congrArg (fun f : (cyclic p) →ₗ[ℂ] (cyclic p) => f v) h

private theorem idem (x a : Fin n) (v : cyclic p) : U p x a (U p x a v) = U p x a v :=
  congrArg (fun f : (cyclic p) →ₗ[ℂ] (cyclic p) => f v)
    (restricted_projection p (false,x) a).1

private theorem sums (x : Fin n) (v : cyclic p) :
    (∑ a, U p x a v) = v ∧ (∑ a, U p a x v) = v := by
  constructor
  · apply Subtype.ext
    change (cyclic p).subtype (∑ a, U p x a v) = (v : K)
    rw [map_sum]
    exact (magic_sums p x v).1
  · apply Subtype.ext
    change (cyclic p).subtype (∑ a, U p a x v) = (v : K)
    rw [map_sum]
    exact (magic_sums p x v).2

/-- Right multiplication by U_yb and left multiplication by U_xa isolate
one summand on either side of the intertwining relation. -/
private theorem sandwich {A B : Mat n} (h : Intertwines p A B)
    (x y a b : Fin n) (v : cyclic p) :
    A x y • U p x a (U p y b v) = B a b • U p x a (U p y b v) := by
  have leftCollapse :
      (∑ z, A x z • U p z b (U p y b v)) = A x y • U p y b v := by
    calc
      _ = A x y • U p y b (U p y b v) := Finset.sum_eq_single y
        (fun z _ hzy => by
          rw [eval_zero p (magic_orthogonal p b z y hzy).2, smul_zero]) (by simp)
      _ = _ := by rw [idem]
  have rightCollapse :
      (∑ c, B c b • U p x a (U p x c (U p y b v))) =
      B a b • U p x a (U p y b v) := by
    calc
      _ = B a b • U p x a (U p x a (U p y b v)) := Finset.sum_eq_single a
        (fun c _ hca => by
          rw [eval_zero p (magic_orthogonal p x a c (Ne.symm hca)).1, smul_zero])
        (by simp)
      _ = _ := by rw [idem]
  have t := congrArg (U p x a) (h x b (U p y b v))
  simp only [leftCollapse, map_sum, map_smul] at t
  exact t.trans rightCollapse

theorem compatible_of_intertwines {A B : Mat n} (h : Intertwines p A B) :
    Compatible p A B := by
  intro x y a b ne
  apply LinearMap.ext
  intro v
  change U p x a (U p y b v) = 0
  have hz : (A x y - B a b) • U p x a (U p y b v) = 0 := by
    rw [sub_smul, sandwich p h x y a b v, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ne)

theorem intertwines_of_compatible {A B : Mat n} (h : Compatible p A B) :
    Intertwines p A B := by
  intro x b v
  calc
    (∑ y, A x y • U p y b v) =
        ∑ y, ∑ a, A x y • U p x a (U p y b v) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.smul_sum, (sums p x (U p y b v)).1]
    _ = ∑ y, ∑ a, B a b • U p x a (U p y b v) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro a _
      by_cases e : A x y = B a b
      · rw [e]
      · simp [eval_zero p (h x y a b e)]
    _ = ∑ a, ∑ y, B a b • U p x a (U p y b v) := Finset.sum_comm
    _ = ∑ a, B a b • U p x a v := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.smul_sum, ← map_sum, (sums p b v).2]

theorem criterion (A B : Mat n) : Intertwines p A B ↔ Compatible p A B :=
  ⟨compatible_of_intertwines p, intertwines_of_compatible p⟩

/-- Any common entrywise scalar function can refine two existing tests. -/
theorem entrywise₂ {A B C D : Mat n} (f : ℂ → ℂ → ℂ)
    (hA : Intertwines p A B) (hC : Intertwines p C D) :
    Intertwines p (fun i j => f (A i j) (C i j))
                 (fun i j => f (B i j) (D i j)) := by
  apply intertwines_of_compatible p
  intro x y a b mismatch
  by_cases first : A x y = B a b
  · by_cases second : C x y = D a b
    · exact (mismatch (congrArg₂ f first second)).elim
    · exact compatible_of_intertwines p hC x y a b second
  · exact compatible_of_intertwines p hA x y a b first

theorem hadamard {A B C D : Mat n}
    (hA : Intertwines p A B) (hC : Intertwines p C D) :
    Intertwines p (fun i j => A i j * C i j) (fun i j => B i j * D i j) :=
  entrywise₂ p (· * ·) hA hC

private theorem weighted_swap (s t : Fin n → ℂ) (z : Fin n → Fin n → cyclic p) :
    (∑ i, s i • ∑ j, t j • z i j) = ∑ j, t j • ∑ i, s i • z i j := by
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl
    (fun i _ => smul_comm (s i) (t j) (z i j)))

theorem matrix_mul {A B C D : Mat n}
    (hA : Intertwines p A B) (hC : Intertwines p C D) :
    Intertwines p (A * C) (B * D) := by
  intro x b v
  calc
    (∑ y, (A*C) x y • U p y b v) =
        ∑ z, A x z • ∑ y, C z y • U p y b v := by
      simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
      exact Finset.sum_comm
    _ = ∑ z, A x z • ∑ c, D c b • U p z c v :=
      Finset.sum_congr rfl (fun z _ => congrArg (fun q => A x z • q) (hC z b v))
    _ = ∑ c, D c b • ∑ z, A x z • U p z c v :=
      weighted_swap p _ _ _
    _ = ∑ c, D c b • ∑ a, B a c • U p x a v :=
      Finset.sum_congr rfl (fun c _ => congrArg (fun q => D c b • q) (hA x c v))
    _ = ∑ a, (B*D) a b • U p x a v := by
      simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl
        (fun c _ => smul_comm (D c b) (B a c) (U p x a v)))

/-- The observed adjacency and diagonal colors generate the initial binary tests. -/
def adjacency (J : Graph n) : Mat n := fun x y => if J.edge x y = true then 1 else 0

theorem initial_adjacency : Intertwines p (adjacency G) (adjacency H) := by
  apply intertwines_of_compatible p
  intro x y a b bad
  apply restricted_mismatch p (false,x) (false,y) a b
  intro same
  have e : G.edge x y = H.edge a b := congrArg (fun t : Bool × Bool => t.2) same
  exact bad (by simp [adjacency, e])

theorem initial_diagonal : Intertwines p (1 : Mat n) (1 : Mat n) := by
  apply intertwines_of_compatible p
  intro x y a b bad
  apply restricted_mismatch p (false,x) (false,y) a b
  intro same
  have e : decide (x=y) = decide (a=b) :=
    congrArg (fun t : Bool × Bool => t.1) same
  by_cases hx : x=y <;> by_cases ha : a=b <;> simp_all [Matrix.one_apply]

theorem initial_full (c : ℂ) :
    Intertwines p (fun _ _ => c) (fun _ _ => c) :=
  intertwines_of_compatible p (fun _ _ _ _ ne => (ne rfl).elim)

private theorem reverse_product {x y a b : Fin n}
    (zeroYX : (U p y b).comp (U p x a) = 0) :
    (U p x a).comp (U p y b) = 0 := by
  apply LinearMap.ext
  intro v
  let z := U p x a (U p y b v)
  have inn : @inner ℂ K _ (z : K) (z : K) = 0 := by
    calc
      _ = @inner ℂ K _ (U p y b v : K) (U p x a z : K) :=
        (restricted_projection p (false,x) a).2 _ _
      _ = @inner ℂ K _ (v : K) (U p y b (U p x a z) : K) :=
        (restricted_projection p (false,y) b).2 _ _
      _ = 0 := by rw [eval_zero p zeroYX]; simp
  apply Subtype.ext
  exact inner_self_eq_zero.mp inn

theorem conjugate_transpose {A B : Mat n} (h : Intertwines p A B) :
    Intertwines p A.conjTranspose B.conjTranspose := by
  apply intertwines_of_compatible p
  intro x y a b bad
  have ne : A y x ≠ B b a := by
    intro e
    exact bad (by simp only [Matrix.conjTranspose_apply, e])
  exact reverse_product p (compatible_of_intertwines p h y x b a ne)

/-- Matrix expressions that can be evaluated on either input graph with the
same constants and scalar tests. Ordinary products give all two-step counts.
Scalar tests can pick out any chosen value. -/
inductive Recipe where
  | diag
  | edge
  | constant (c : ℂ)
  | product (left right : Recipe)
  | entrywise (f : ℂ → ℂ → ℂ) (left right : Recipe)
  | adjoint (e : Recipe)

def Recipe.eval (J : Graph n) : Recipe → Mat n
  | .diag => 1
  | .edge => adjacency J
  | .constant c => fun _ _ => c
  | .product l r => l.eval J * r.eval J
  | .entrywise f l r => fun i j => f (l.eval J i j) (r.eval J i j)
  | .adjoint e => (e.eval J).conjTranspose

theorem eval_intertwines (e : Recipe) : Intertwines p (e.eval G) (e.eval H) := by
  induction e with
  | diag => exact initial_diagonal p
  | edge => exact initial_adjacency p
  | constant c => exact initial_full p c
  | product _ _ hl hr => exact matrix_mul p hl hr
  | entrywise f _ _ hl hr => exact entrywise₂ p f hl hr
  | adjoint _ h => exact conjugate_transpose p h

/-- Indicator that the number of l-then-r two-step paths equals k, whenever l
and r are indicator matrices. -/
def twoStepCell (l r : Recipe) (k : Nat) : Recipe := by
  classical
  exact .entrywise (fun v _ => if v = (k : ℂ) then 1 else 0)
    (.product l r) (.constant 0)

/-- Restrict an old color to one complete finite list of two-step count tests. -/
def refineCell (old : Recipe) : List (Recipe × Recipe × Nat) → Recipe
  | [] => old
  | (l,r,k) :: rest =>
      .entrywise (· * ·) (twoStepCell l r k) (refineCell old rest)

theorem refined_cells_intertwine (old : Recipe) (tests : List (Recipe × Recipe × Nat)) :
    Intertwines p ((refineCell old tests).eval G) ((refineCell old tests).eval H) :=
  eval_intertwines p (refineCell old tests)

end QGI.Intertwiner
