import Orders.Order22
import ProfileCoverage

namespace QGI

theorem noSeparation23 : NoSeparation 23 := by
  intro G H q
  by_contra bad
  obtain ⟨xs,hm,_⟩ := Coherent.ProfileCoverage.profile_of_counterexample
    (by decide : 16 ≤ 23) (by decide : 23 ≤ 23) q bad
  change xs ∈ Coherent.ProfileCoverage.residual 23 at hm
  have empty : Coherent.ProfileCoverage.residual 23=[] := Coherent.ProfileCoverage.all_covered (7 : Fin 8)
  rw [empty] at hm
  exact List.not_mem_nil hm

theorem through23 : Through 23 :=
  (through_succ_iff 22).mpr ⟨through22,noSeparation23⟩

end QGI
