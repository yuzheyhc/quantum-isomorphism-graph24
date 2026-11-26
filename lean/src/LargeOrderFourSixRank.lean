import RegionalFourSixEightTetra
import SixSixEightPins

namespace QGI.Coherent.LargeOrderFourSixRank
open SixTenCoordinates FourSixSix
open SixEightGeometry (rect)
open SixSixEightPins (Flat)

private def score (j : Fin 6) (v : Fin 4 → Bool) : Nat :=
  ∑ i, if incident i j ∧ v i=true then 1 else 0

private theorem rank : ∀ a b : Fin 4 → Bool, (∀ i j, score i a=score j b) → ∀ i j, a i=b j := by
  native_decide

/-- Uniformity against the six tetrahedron edges is already uniformity
against the four vertices, by the rank of the unsigned incidence matrix. -/
theorem uniform {n l r t k : Nat} [NeZero k] {c : Fin n → Fin n → Nat} (law : Laws c c)
    (F : Shore c l (Fin 4)) (S : Shore c r (Fin 6)) (Y : Shore c t (Fin k))
    (v : Nat) (perm : Equiv.Perm (Fin 6)) (inc : ∀ i j, rect F S i j=v ↔ incident i (perm j))
    (flat : ∀ i j, rect S Y i j=rect S Y 0 0) : ∀ i j, rect F Y i j=rect F Y 0 0 := by
  let Z := fun i j => decide (incident i (perm j))
  let M := fun i j => decide (rect F Y i j=rect F Y 0 0)
  have mk : Block F F S S Z Z := by
    intro i j a b h
    apply decide_eq_decide.mpr
    change rect F S i j=rect F S a b at h
    rw [←inc,←inc,h]
  have bits : Block F F Y Y M M := fun ⦃_ _ _ _⦄ h => congrArg (fun q => decide (q=rect F Y 0 0)) h
  have prod := Block.fold law (Block.flip law mk) bits (fun a b => if a=true ∧ b=true then 1 else 0)
  intro i j
  have eq : ∀ a b, score a (fun k => M k j)=score b (fun k => M k 0) := by
    intro a b
    simpa only [score,Z,decide_eq_true_eq,Equiv.apply_symm_apply] using
      prod ((flat (perm.symm a) j).trans (flat (perm.symm b) 0).symm)
  exact of_decide_eq_true ((rank _ _ eq i 0).trans (by simp [M]))

end QGI.Coherent.LargeOrderFourSixRank
