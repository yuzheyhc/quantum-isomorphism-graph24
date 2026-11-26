import StrategyColorLaws
import QuantumIsoSymmetry

noncomputable section
namespace QGI.Coherent.StrategyOrientation
open Intertwiner StrategyColors StrategyColorLaws
variable {n : Nat} {G H : Graph n} {K V : Type}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (p : PerfectStrategy G H K) (q : PerfectStrategy H G V)

private def paired : CoherentAlgebra n where
  space := {
    carrier := {A | ∃ B ∈ (closure H).space, Intertwines p A B ∧ Intertwines q B A}
    zero_mem' := ⟨0,(closure H).space.zero_mem,initial_full p 0,initial_full q 0⟩
    add_mem' := by
      rintro _ _ ⟨B,hB,h,t⟩ ⟨D,hD,g,u⟩
      exact ⟨B+D,(closure H).space.add_mem hB hD,entrywise₂ p (·+·) h g,entrywise₂ q (·+·) t u⟩
    smul_mem' := by
      rintro c _ ⟨B,hB,h,t⟩
      exact ⟨c • B,(closure H).space.smul_mem c hB,entrywise₂ p (fun x _ => c • x) h h,entrywise₂ q (fun x _ => c • x) t t⟩ }
  one_mem := ⟨1,(closure H).one_mem,initial_diagonal p,initial_diagonal q⟩
  ones_mem := ⟨ones n,(closure H).ones_mem,initial_full p 1,initial_full q 1⟩
  mul_mem := by
    rintro _ _ ⟨B,hB,h,t⟩ ⟨D,hD,g,u⟩
    exact ⟨B*D,(closure H).mul_mem hB hD,matrix_mul p h g,matrix_mul q t u⟩
  schur_mem := by
    rintro _ _ ⟨B,hB,h,t⟩ ⟨D,hD,g,u⟩
    exact ⟨schur B D,(closure H).schur_mem hB hD,hadamard p h g,hadamard q t u⟩
  adjoint_mem := by
    rintro _ ⟨B,hB,h,t⟩
    exact ⟨B.conjTranspose,(closure H).adjoint_mem hB,conjugate_transpose p h,conjugate_transpose q t⟩

/-- Evaluating the same coherent algebra expressions in both graphs forces
oppositely oriented perfect strategies to identify inverse color names. -/
theorem reverse {i j a b : Fin n} (h : Relations.color (closure G) i j = targetName p a b) :
    Relations.color (closure H) a b = targetName q i j := by
  obtain ⟨x,y,hit⟩ := exists_target q a b
  have same : Relations.color (closure G) x y=Relations.color (closure G) i j := by
    apply (Relations.same _ _ _ _ _).mpr
    intro A hA
    obtain ⟨B,hB,t,u⟩ := hA (paired p q)
      ⟨adjacency H,adjacency_mem H,initial_adjacency p,initial_adjacency q⟩
    exact (entry_eq q u hit).symm.trans (entries p h hB t).symm
  exact (associated q).mpr ((maps_support q hit).trans (Subtype.ext same))

end QGI.Coherent.StrategyOrientation
