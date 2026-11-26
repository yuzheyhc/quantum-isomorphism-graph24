import CoherentHomogeneous

noncomputable section

namespace QGI.Coherent
open Intertwiner

variable {n : Nat} {G H : Graph n} {K : Type}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Target matrices with a corresponding matrix in the source coherent
closure form a coherent algebra, with the correspondence witnessed by the
measurement operators of the given strategy. -/
private def intertwinedTargets (p : PerfectStrategy G H K) : CoherentAlgebra n where
  space := {
    carrier := {B | ∃ A ∈ (closure G).space, Intertwines p A B}
    zero_mem' := ⟨0, (closure G).space.zero_mem, initial_full p 0⟩
    add_mem' := by
      rintro _ _ ⟨A, ha, hp⟩ ⟨C, hc, hq⟩
      exact ⟨A + C, (closure G).space.add_mem ha hc, entrywise₂ p (· + ·) hp hq⟩
    smul_mem' := by
      rintro c _ ⟨A, ha, hp⟩
      exact ⟨c • A, (closure G).space.smul_mem c ha, entrywise₂ p (fun x _ => c • x) hp hp⟩ }
  one_mem := ⟨1, (closure G).one_mem, initial_diagonal p⟩
  ones_mem := ⟨ones n, (closure G).ones_mem, initial_full p 1⟩
  mul_mem := by
    rintro _ _ ⟨A, ha, hp⟩ ⟨C, hc, hq⟩
    exact ⟨A * C, (closure G).mul_mem ha hc, matrix_mul p hp hq⟩
  schur_mem := by
    rintro _ _ ⟨A, ha, hp⟩ ⟨C, hc, hq⟩
    exact ⟨schur A C, (closure G).schur_mem ha hc, hadamard p hp hq⟩
  adjoint_mem := by
    rintro _ ⟨A, ha, hp⟩
    exact ⟨A.conjTranspose, (closure G).adjoint_mem ha, conjugate_transpose p hp⟩

theorem exists_mem_intertwines_of_mem_closure (p : PerfectStrategy G H K) {B : Mat n}
    (hB : B ∈ (closure H).space) : ∃ A ∈ (closure G).space, Intertwines p A B :=
  hB (intertwinedTargets p) ⟨adjacency G, adjacency_mem G, initial_adjacency p⟩

theorem exists_intertwining_source (p : PerfectStrategy G H K) {B : Mat n}
    (hB : B ∈ (closure H).space) : ∃ A, Intertwines p A B := by
  obtain ⟨A, _, h⟩ := exists_mem_intertwines_of_mem_closure p hB
  exact ⟨A, h⟩

end QGI.Coherent
