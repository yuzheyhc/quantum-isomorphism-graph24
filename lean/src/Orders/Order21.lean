import Orders.Order20
import ProfileCoverage

namespace QGI

theorem noSeparation21 : NoSeparation 21 := by
  intro G H q
  by_contra bad
  obtain ⟨xs,hm,_⟩ := Coherent.ProfileCoverage.profile_of_counterexample
    (by decide : 16 ≤ 21) (by decide : 21 ≤ 23) q bad
  change xs ∈ Coherent.ProfileCoverage.residual 21 at hm
  have empty : Coherent.ProfileCoverage.residual 21=[] := by native_decide
  rw [empty] at hm
  exact List.not_mem_nil hm

theorem through21 : Through 21 :=
  (through_succ_iff 20).mpr ⟨through20,noSeparation21⟩

end QGI
