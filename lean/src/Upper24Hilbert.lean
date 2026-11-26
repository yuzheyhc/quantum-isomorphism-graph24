import QuantumGraph
import Upper24

/-! The finite-dimensional strategy on the Hilbert space of four-by-four matrices. -/
noncomputable section
open scoped BigOperators
namespace Upper24Hilbert
open Upper24

abbrev D := Fin 4
abbrev Mat := Matrix D D ℂ
abbrev K := EuclideanSpace ℂ (D × D)

/-- Hilbert-Schmidt coordinates, with (row,column) as a single orthonormal index. -/
def coord : K ≃ₗ[ℂ] Mat where
  toFun v := fun i j => v (i,j)
  invFun A := (WithLp.equiv 2 ((D × D) → ℂ)).symm (fun ij => A ij.1 ij.2)
  left_inv v := by ext ij; rfl
  right_inv A := by ext i j; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def leftLin (A : Mat) : Mat →ₗ[ℂ] Mat where
  toFun B := A * B
  map_add' _ _ := mul_add _ _ _
  map_smul' t B := Matrix.mul_smul A t B

def rightLin (A : Mat) : Mat →ₗ[ℂ] Mat where
  toFun B := B * A
  map_add' _ _ := add_mul _ _ _
  map_smul' t B := Matrix.smul_mul t B A

def L (A : Mat) : K →L[ℂ] K :=
  LinearMap.toContinuousLinearMap
    ((coord.symm.toLinearMap.comp (leftLin A)).comp coord.toLinearMap)

def R (A : Mat) : K →L[ℂ] K :=
  LinearMap.toContinuousLinearMap
    ((coord.symm.toLinearMap.comp (rightLin A)).comp coord.toLinearMap)

@[simp] theorem coordL (A : Mat) (v : K) : coord (L A v) = A * coord v := by
  change coord (coord.symm (A * coord v)) = _
  exact coord.apply_symm_apply _
@[simp] theorem coordR (A : Mat) (v : K) : coord (R A v) = coord v * A := by
  change coord (coord.symm (coord v * A)) = _
  exact coord.apply_symm_apply _

theorem LR (A B : Mat) (v : K) : L A (R B v) = R B (L A v) := by
  apply coord.injective
  simp [mul_assoc]

theorem inner_coord (v w : K) :
    @inner ℂ K _ v w = ((coord v).conjTranspose * coord w).trace := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [RCLike.inner_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_four]
  dsimp [coord] <;> ring

theorem leftAdj (A : Mat) (h : A.conjTranspose = A) (v w : K) :
    @inner ℂ K _ (L A v) w = @inner ℂ K _ v (L A w) := by
  simp only [inner_coord, coordL, Matrix.conjTranspose_mul, h, mul_assoc]
theorem rightAdj (A : Mat) (h : A.conjTranspose = A) (v w : K) :
    @inner ℂ K _ (R A v) w = @inner ℂ K _ v (R A w) := by
  simp only [inner_coord, coordR, Matrix.conjTranspose_mul, h]
  rw [mul_assoc, Matrix.trace_mul_comm A, mul_assoc]

def liftNum (N : Upper24.M) : Mat :=
  fun i j => (N i.val j.val : ℂ) / 4

def P (x a : V) : Mat := liftNum (num x.val a.val)

theorem mulEntry (A B : Upper24.M) (i j : D) :
    (liftNum A * liftNum B) i j =
      (Upper24.mul A B i.val j.val : ℂ) / 16 := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, liftNum, Upper24.mul, show (3 : D).val=3 from rfl] <;>
    push_cast <;> ring

theorem Psymm (x a : V) : (P x a).conjTranspose = P x a := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.conjTranspose_apply, P, liftNum]
  rw [(projectors x a j i).1]
  simp

theorem Pidem (x a : V) : P x a * P x a = P x a := by
  apply Matrix.ext
  intro i j
  unfold P
  rw [mulEntry, (projectors x a i j).2]
  simp [liftNum] <;> push_cast <;> ring

theorem Pzero (x a y b : V) (bad : kind false x y ≠ kind true a b) :
    P x a * P y b = 0 := by
  apply Matrix.ext
  intro i j
  unfold P
  rw [mulEntry, mismatch x a y b bad i j]
  simp

private theorem intRows : ∀ x : V, ∀ i j : D,
    (∑ a : V, num x.val a.val i.val j.val) = 4 * (if i = j then 1 else 0) ∧
    (∑ a : V, num a.val x.val i.val j.val) = 4 * (if i = j then 1 else 0) := by
  native_decide

theorem row (x : V) : ∑ a : V, P x a = 1 := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.sum_apply, P, liftNum]
  rw [← Finset.sum_div, ← Int.cast_sum, (intRows x i j).1]
  by_cases h : i = j <;> simp [h, Matrix.one_apply]
theorem col (x : V) : ∑ a : V, P a x = 1 := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.sum_apply, P, liftNum]
  rw [← Finset.sum_div, ← Int.cast_sum, (intRows x i j).2]
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

abbrev Q := QGI.Question 24
def T (q : Q) (a : V) : Mat :=
  let e := QGI.ends q a
  P e.1 e.2

theorem orthT (q : Q) (a b : V) (hne : a ≠ b) : T q a * T q b = 0 := by
  rcases q with ⟨side, x⟩
  cases side
  · apply Pzero
    have e₁ := (simpleKinds false x x).1.mpr rfl
    have e₂ := (simpleKinds true a b).1
    intro eq
    exact hne (e₂.mp (eq.symm.trans e₁))
  · apply Pzero
    have e₁ := (simpleKinds false a b).1
    have e₂ := (simpleKinds true x x).1.mpr rfl
    intro eq
    exact hne (e₁.mp (eq.trans e₂))

theorem sumT (q : Q) : ∑ a : V, T q a = 1 := by
  rcases q with ⟨side,x⟩
  cases side <;> simp [T, QGI.ends, row, col]

theorem leftPVM (q : Q) : QGI.IsPVM (fun a => L (T q a)) where
  selfAdjoint a := leftAdj _ (Psymm _ _)
  idempotent a v := by
    apply coord.injective
    simp only [coordL, ← mul_assoc, T, Pidem]
  orthogonal a b hb v := by
    apply coord.injective
    simp [← mul_assoc, orthT q a b hb]
  complete v := by
    apply coord.injective
    simp only [map_sum, coordL, ← Finset.sum_mul, sumT, one_mul]

theorem rightPVM (q : Q) : QGI.IsPVM (fun a => R (T q a)) where
  selfAdjoint a := rightAdj _ (Psymm _ _)
  idempotent a v := by
    apply coord.injective
    simp only [coordR, mul_assoc, T, Pidem]
  orthogonal a b hb v := by
    apply coord.injective
    simp [mul_assoc, orthT q b a (Ne.symm hb)]
  complete v := by
    apply coord.injective
    simp only [map_sum, coordR, ← Finset.mul_sum, sumT, mul_one]

def psi : K := coord.symm ((1/2 : ℂ) • (1 : Mat))

theorem psi_norm : ‖psi‖ = 1 := by
  have h : ‖psi‖^2=1 := by
    rw [@norm_sq_eq_re_inner ℂ K _ _ _ psi,inner_coord]
    norm_num [psi, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.conjTranspose_apply]
  nlinarith [norm_nonneg psi]

theorem jointOnState (A B : Mat) :
    coord (L A (R B psi)) = (1/2 : ℂ) • (A * B) := by
  simp [psi, Matrix.smul_mul, Matrix.mul_smul]

private theorem typeEquivalence : ∀ x y a b : V,
    kind false x y = kind true a b ↔
    QGI.rel (graph false) x y = QGI.rel (graph true) a b := by
  native_decide

/-- This field-by-field construction has no strategy or existence premise. -/
def strategy : QGI.PerfectStrategy (graph false) (graph true) K where
  psi := psi
  norm_psi := psi_norm
  alice q a := L (T q a)
  bob q a := R (T q a)
  alicePVM := leftPVM
  bobPVM := rightPVM
  commute q r a b v := LR _ _ v
  perfect q r a b lose := by
    let e := QGI.ends q a
    let f := QGI.ends r b
    have bad : kind false e.1 f.1 ≠ kind true e.2 f.2 :=
      fun eq => lose ((typeEquivalence e.1 f.1 e.2 f.2).mp eq)
    have zeroMul : T q a * T r b = 0 := Pzero _ _ _ _ bad
    apply coord.injective
    rw [jointOnState, zeroMul, smul_zero, map_zero]

theorem existsSeparation24 : QGI.Separation 24 := by
  refine ⟨graph false, graph true, ?_, graphsNotIsomorphic⟩
  exact ⟨K, inferInstance, inferInstance, inferInstance, ⟨strategy⟩⟩

end Upper24Hilbert
