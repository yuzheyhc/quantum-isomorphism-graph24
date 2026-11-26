import SixteenCoverage

namespace QGI

/-- Every pair of commuting-quantum-isomorphic ordinary graphs on sixteen
vertices admits an ordinary graph isomorphism. -/
theorem noSeparation16 : NoSeparation 16 := by
  intro G H quantum
  by_contra bad
  obtain ⟨xs,mem,_⟩ := Coherent.SixteenCoverage.profile_of_counterexample quantum bad
  rw [Coherent.SixteenCoverage.no_remaining] at mem
  exact List.not_mem_nil mem

theorem through16 : Through 16 :=
  (through_succ_iff 15).mpr ⟨through15,noSeparation16⟩

end QGI
