import FifteenNamed
import SeventeenComponents
import SeventeenHard
import SeventeenHardSix
import SeventeenHardEight

namespace QGI
open Coherent Coherent.CoprimeProfiles

private def seventeenCovered (xs : List Nat) : Bool :=
  checkFrom 4 xs || decide ((xs.filter (fun k => 3<k)).sum=14) ||
    decide ((xs.filter (fun k => 3<k)).sum=15) ||
    decide (xs=[17] ∨ xs=[1,16] ∨ xs=[2,15] ∨ xs=[1,1,15] ∨ xs=[1,4,12] ∨
      xs=[1,6,10] ∨ xs=[1,8,8] ∨ xs=[1,4,4,4,4] ∨ xs=[1,4,4,8] ∨ xs=[1,4,6,6])

private theorem complete_cases : (Routes.enumerate 17 1 17).filter (fun s => !(seventeenCovered s))=[] := by
  native_decide

/-- Every commuting-quantum-isomorphic pair of ordinary graphs on
seventeen vertices admits an ordinary vertex isomorphism. -/
theorem noSeparation17 : NoSeparation 17 := by
  classical
  intro G H q
  obtain ⟨xs,mem,⟨P⟩⟩ := extract G
  have checked : seventeenCovered xs = true := by
    cases h : seventeenCovered xs with
    | true => rfl
    | false =>
      have bad : xs ∈ (Routes.enumerate 17 1 17).filter (fun s => !(seventeenCovered s)) :=
        List.mem_filter.mpr ⟨mem,by simp [h]⟩
      rw [complete_cases] at bad
      exact (List.not_mem_nil bad).elim
  simp only [seventeenCovered,Bool.or_eq_true,decide_eq_true_eq] at checked
  rcases checked with ((small|fourteen)|fifteen)|other
  · exact LargeCoreProfiles.isomorphic P small q
  · exact ZivAv.isomorphic P fourteen q
  · exact Fifteen.isomorphic P fifteen q
  rcases other with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact isomorphic_of_homogeneous (Or.inl rfl) P.homogeneous q
  · exact Components.of_coprime_pair P (by decide) (by decide) (by decide) q
  · exact Components.of_coprime_pair P (by decide) (by decide) (by decide) q
  · exact Components.two_singletons_fifteen P q
  · exact SingletonSwitch.three_fibers through16 P (by decide) (by decide) (by decide) q
  · exact SingletonSwitch.three_fibers through16 P (by decide) (by decide) (by decide) q
  · exact SingletonSwitch.three_fibers through16 P (by decide) (by decide) (by decide) q
  · exact SeventeenHard.four_fours P q
  · exact SeventeenHardEight.four_four_eight P q
  · exact SeventeenHardSix.four_six_six P q

theorem through17 : Through 17 :=
  (through_succ_iff 16).mpr ⟨through16,noSeparation17⟩

end QGI
