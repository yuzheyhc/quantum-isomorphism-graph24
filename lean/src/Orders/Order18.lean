import ProfileCoverage
import RegionalSixTwelveComplete

namespace QGI

theorem noSeparation18 : NoSeparation 18 := by
  intro G H q
  by_contra bad
  obtain ⟨xs,hm,⟨P⟩⟩ := Coherent.ProfileCoverage.profile_of_counterexample
    (by decide : 16 ≤ 18) (by decide : 18 ≤ 23) q bad
  change xs ∈ Coherent.ProfileCoverage.residual 18 at hm
  have rest : (Coherent.ProfileCoverage.residual 18).all (fun s => s == [6,12]) = true := by native_decide
  have eq : xs = [6,12] := beq_iff_eq.mp (List.all_eq_true.mp rest xs hm)
  subst xs
  exact bad (Coherent.RegionalSixTwelve.isomorphic P (by decide) (by decide) (by decide) q)

theorem through18 : Through 18 :=
  (through_succ_iff 17).mpr ⟨through17,noSeparation18⟩

end QGI
