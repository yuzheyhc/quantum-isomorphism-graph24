import Orders.Order21
import ProfileCoverage

namespace QGI

theorem noSeparation22 : NoSeparation 22 := by
  intro G H q
  by_contra bad
  obtain ⟨xs,hm,_⟩ := Coherent.ProfileCoverage.profile_of_counterexample
    (by decide : 16 ≤ 22) (by decide : 22 ≤ 23) q bad
  change xs ∈ Coherent.ProfileCoverage.residual 22 at hm
  have empty : Coherent.ProfileCoverage.residual 22=[] := Coherent.ProfileCoverage.all_covered (6 : Fin 8)
  rw [empty] at hm
  exact List.not_mem_nil hm

theorem through22 : Through 22 :=
  (through_succ_iff 21).mpr ⟨through21,noSeparation22⟩

end QGI
