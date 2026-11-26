import Intertwiner

open scoped BigOperators

noncomputable section
namespace QGI.Intertwiner
open QGI.Synchrony

variable {n : Nat} {G H : Graph n} {K : Type}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The sum of the entries, with both endpoints ordered. -/
def total (A : Mat n) : ℂ := ∑ i, ∑ j, A i j

private def allOnes (n : Nat) : Mat n := fun _ _ => 1

private theorem ones_sandwich (A : Mat n) :
    (allOnes n * A) * allOnes n = fun _ _ => total A := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, allOnes, one_mul, mul_one, total]
  exact Finset.sum_comm

/-- J A J is constant and equals the sum of the entries of A. Intertwining
two such constant matrices gives equal scalars on the unit state. -/
theorem total_eq (p : PerfectStrategy G H K) {A B : Mat n}
    (h : Intertwines p A B) : total A = total B := by
  classical
  cases n with
  | zero => simp [total]
  | succ m =>
    have hj : Intertwines p (allOnes (m+1)) (allOnes (m+1)) := initial_full p 1
    have hs := matrix_mul p (matrix_mul p hj h) hj
    rw [ones_sandwich, ones_sandwich] at hs
    let v : cyclic p := ⟨p.psi, psi_mem p⟩
    let i : Fin (m+1) := 0
    have he := hs i i v
    change (∑ y, total A • U p y i v) = ∑ a, total B • U p i a v at he
    have hk := congrArg (fun w : cyclic p => (cyclic p).subtype w) he
    simp only [map_sum, map_smul] at hk
    change (∑ y, total A • (U p y i v : K)) =
      ∑ a, total B • (U p i a v : K) at hk
    simp only [← Finset.smul_sum] at hk
    rw [(magic_sums p i v).2, (magic_sums p i v).1] at hk
    have hz : (total A - total B) • p.psi = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact hk
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (psi_ne_zero p))

private theorem total_diagonal (A : Mat n) :
    total (fun i j => (1 : Mat n) i j * A i j) = Matrix.trace A := by
  classical
  simp [total, Matrix.one_apply, Matrix.trace, Matrix.diag_apply, ite_mul]

theorem trace_eq (p : PerfectStrategy G H K) {A B : Mat n}
    (h : Intertwines p A B) : Matrix.trace A = Matrix.trace B := by
  simpa only [total_diagonal] using
    (total_eq p (hadamard p (initial_diagonal p) h))

def walk2 (J : Graph n) : Mat n := adjacency J * adjacency J
def walk3 (J : Graph n) : Mat n := walk2 J * adjacency J
def walk6 (J : Graph n) : Mat n := walk3 J * walk3 J
def walk9 (J : Graph n) : Mat n := walk6 J * walk3 J

/-- Trace of A²A⁹, counting closed, rooted, directed walks of length 11. -/
def cycle11Count (J : Graph n) : ℂ := Matrix.trace (walk2 J * walk9 J)

/-- Homomorphisms from the graph with two terminals joined by internally
disjoint paths of lengths 1, 3 and 9. The images of internal vertices are free. -/
def theta139Count (J : Graph n) : ℂ :=
  total (fun i j => adjacency J i j * (walk3 J i j * walk9 J i j))

/-- T records walks along an edge with a choice of common neighbor of its
endpoints. L adds one unconstrained edge. -/
def triangleStep (J : Graph n) : Mat n :=
  let triangles : Mat n := fun i j => adjacency J i j * walk2 J i j
  triangles * adjacency J

/-- Trace of L² for a square with triangles attached along opposite edges. -/
def oppositeTrianglesCount (J : Graph n) : ℂ :=
  Matrix.trace (triangleStep J * triangleStep J)

theorem three_counts_of_strategy (p : PerfectStrategy G H K) :
    cycle11Count G = cycle11Count H ∧
    theta139Count G = theta139Count H ∧
    oppositeTrianglesCount G = oppositeTrianglesCount H := by
  have h1 := initial_adjacency p
  have h2 : Intertwines p (walk2 G) (walk2 H) := matrix_mul p h1 h1
  have h3 : Intertwines p (walk3 G) (walk3 H) := matrix_mul p h2 h1
  have h6 : Intertwines p (walk6 G) (walk6 H) := matrix_mul p h3 h3
  have h9 : Intertwines p (walk9 G) (walk9 H) := matrix_mul p h6 h3
  have hL : Intertwines p (triangleStep G) (triangleStep H) :=
    matrix_mul p (hadamard p h1 h2) h1
  exact ⟨trace_eq p (matrix_mul p h2 h9),
    total_eq p (hadamard p h1 (hadamard p h3 h9)),
    trace_eq p (matrix_mul p hL hL)⟩

theorem three_counts_qc (h : QuantumIso G H) :
    cycle11Count G = cycle11Count H ∧
    theta139Count G = theta139Count H ∧
    oppositeTrianglesCount G = oppositeTrianglesCount H := by
  obtain ⟨K, g, ip, _hc, ⟨p⟩⟩ := h
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  exact three_counts_of_strategy p

theorem cycle11_qc (h : QuantumIso G H) : cycle11Count G = cycle11Count H :=
  (three_counts_qc h).1

theorem theta139_qc (h : QuantumIso G H) : theta139Count G = theta139Count H :=
  (three_counts_qc h).2.1

theorem oppositeTriangles_qc (h : QuantumIso G H) :
    oppositeTrianglesCount G = oppositeTrianglesCount H :=
  (three_counts_qc h).2.2

end QGI.Intertwiner
