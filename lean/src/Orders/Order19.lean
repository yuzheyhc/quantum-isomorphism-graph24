import ProfileCoverage
import RegionalSixTwelveComplete
import Orders.Order18
namespace QGI

theorem noSeparation19 : NoSeparation 19 := by
  intro G H q
  by_contra bad
  obtain ⟨xs,hm,⟨P⟩⟩ := Coherent.ProfileCoverage.profile_of_counterexample
    (by decide : 16 ≤ 19) (by decide : 19 ≤ 23) q bad
  change xs ∈ Coherent.ProfileCoverage.residual 19 at hm
  have rest : (Coherent.ProfileCoverage.residual 19).all (fun s => s == [1,6,12]) = true := by native_decide
  have eq : xs = [1,6,12] := beq_iff_eq.mp (List.all_eq_true.mp rest xs hm)
  subst xs
  exact bad (Coherent.RegionalSixTwelve.isomorphic P (by decide) (by decide) (by decide) q)

theorem through19 : Through 19 :=
  (through_succ_iff 18).mpr ⟨through18,noSeparation19⟩

end QGI
