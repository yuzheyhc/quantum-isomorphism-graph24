import Orders.Order19
import ProfileCoverage

namespace QGI

theorem noSeparation20 : NoSeparation 20 := by
  intro G H q
  by_contra bad
  obtain ⟨xs,hm,_⟩ := Coherent.ProfileCoverage.profile_of_counterexample
    (by decide : 16 ≤ 20) (by decide : 20 ≤ 23) q bad
  change xs ∈ Coherent.ProfileCoverage.residual 20 at hm
  have empty : Coherent.ProfileCoverage.residual 20=[] := by native_decide
  rw [empty] at hm
  exact List.not_mem_nil hm

theorem through20 : Through 20 :=
  (through_succ_iff 19).mpr ⟨through19,noSeparation20⟩

end QGI
