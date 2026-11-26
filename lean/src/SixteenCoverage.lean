import SingleFiberProfile
import ProfileExtraction
import SingletonSwitch
import FiveFiber
import FourteenFiber
import ZivAvCoreQuantum
import FourFourEightQuantum
import LargeCoreProfiles
import SmallFiberElimination
import DoubleEightQuantum
import SixTenQuantum
import FourTwelveQuantum
import FourSixSixComplete
import FourFiberSixteen

namespace QGI.Coherent.SixteenCoverage
open CoprimeProfiles

private def otherSizes : List (Nat × Nat) := [(2,13),(3,12),(4,11),(5,10),(6,9),(7,8)]

private def singletonPair (xs : List Nat) : Bool := otherSizes.any (fun ab => [1,ab.1,ab.2] == xs)

private theorem of_singleton_pair {G H : Graph 16} {xs : List Nat} (P : Profile G xs)
    (yes : singletonPair xs = true) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨⟨a,b⟩,member,eq⟩ := List.any_eq_true.mp yes
  obtain rfl : [1,a,b] = xs := beq_iff_eq.mp eq
  have facts : ∀ k ∈ otherSizes, 1 < k.1 ∧ 1 < k.2 ∧ k.1 + k.2 = 15 := by decide
  obtain ⟨ha,hb,sum⟩ := facts _ member
  obtain ⟨x,hx⟩ := P.fiber_of_mem (m := 1) (by simp) (by decide)
  obtain ⟨i,hi⟩ := P.fiber_of_mem (m := a) (by simp) (by omega)
  obtain ⟨j,hj⟩ := P.fiber_of_mem (m := b) (by simp) (by omega)
  exact SingletonSwitch.isomorphic_of_three_sizes x i j hx (by simpa only [hi] using ha)
    (by simpa only [hj] using hb) (by simpa only [hi,hj] using sum) q

/-- A sufficient test for a source profile. Each alternative has a graph
theorem whose only other input is a commuting perfect strategy. -/
def covered (xs : List Nat) : Bool := checkFrom 4 xs || decide (3 ∈ xs) || xs.all (· ≤ 4) ||
  decide (xs = [16] ∨ xs = [8,8] ∨ xs = [6,10] ∨ xs = [4,12] ∨ xs = [4,6,6]) || singletonPair xs ||
  decide (5 ∈ xs ∨ 14 ∈ xs ∨ 15 ∈ xs) ||
  decide ((xs.filter (fun k => 3 < k)).sum=14 ∨ xs=[4,4,8])

theorem isomorphic {G H : Graph 16} {xs : List Nat} (P : Profile G xs)
    (yes : covered xs = true) (q : QuantumIso G H) : Isomorphic G H := by
  classical
  simp only [covered,Bool.or_eq_true,decide_eq_true_eq,List.all_eq_true] at yes
  rcases yes with yes | (core | special)
  case inr.inl => exact ZivAv.isomorphic P core q
  case inr.inr =>
    subst xs
    obtain ⟨a,ha⟩ := P.occurs ⟨0,by decide⟩ (by decide)
    obtain ⟨b,hb⟩ := P.occurs ⟨1,by decide⟩ (by decide)
    obtain ⟨y,hy⟩ := P.occurs ⟨2,by decide⟩ (by decide)
    apply FourFourEight.isomorphic_of_four_four_eight a b y _ _ _ _ q
    · rw [P.fiber_size,ha]; decide
    · rw [P.fiber_size,hb]; decide
    · rw [P.fiber_size,hy]; decide
    · intro inside
      have eq := (P.same a b).mpr ((Relations.same _ _ _ _ _).mpr (mem_fiber.mp inside))
      rw [ha,hb] at eq
      exact (by decide : (0 : Fin 3) ≠ 1) eq
  rcases yes with yes | (five | fourteen | fifteen)
  case inr.inl =>
    obtain ⟨a,h⟩ := P.fiber_of_mem five (by decide)
    exact FiveFiber.isomorphic_of_five a h q
  case inr.inr.inl =>
    obtain ⟨a,h⟩ := P.fiber_of_mem fourteen (by decide)
    exact FourteenFiber.isomorphic_of_fourteen a h q
  case inr.inr.inr =>
    obtain ⟨a,h⟩ := P.fiber_of_mem fifteen (by decide)
    exact FourteenFiber.isomorphic_of_fifteen a h q
  rcases yes with yes | pair
  case inr => exact of_singleton_pair P pair q
  rcases yes with (((small | three) | tiny) | full)
  · exact LargeCoreProfiles.isomorphic P small q
  · obtain ⟨b,h⟩ := P.fiber_of_mem three (by decide)
    exact SmallFiberElimination.isomorphic_of_three b h q
  · apply FourFiberSixteen.isomorphic_of_max_four _ q
    intro i
    rw [P.fiber_size]
    exact tiny _ (List.getElem_mem _)
  rcases full with rfl | rfl | rfl | rfl | rfl
  · exact P.isomorphic_single_sixteen q
  · apply DoubleEightGraphs.isomorphic_of_two_eights _ q
    intro i
    rw [P.fiber_size]
    exact (show ∀ k : Fin 2, ([8,8] : List Nat)[k.val] = 8 by decide) (P.tag i)
  · exact SixTenGraphs.isomorphic_of_six_and_ten (P.fiber_of_mem (by decide) (by decide))
      (P.fiber_of_mem (by decide) (by decide)) q
  · exact FourTwelveQuantum.isomorphic_of_four_and_twelve (P.fiber_of_mem (by decide) (by decide))
      (P.fiber_of_mem (by decide) (by decide)) q
  · obtain ⟨a,ha⟩ := P.occurs ⟨0,by decide⟩ (by decide)
    obtain ⟨b,hb⟩ := P.occurs ⟨1,by decide⟩ (by decide)
    obtain ⟨z,hz⟩ := P.occurs ⟨2,by decide⟩ (by decide)
    apply FourSixSix.isomorphic_of_four_six_six a b z _ _ _ _ q
    · rw [P.fiber_size,ha]; decide
    · rw [P.fiber_size,hb]; decide
    · rw [P.fiber_size,hz]; decide
    · intro inside
      have eq := (P.same b z).mpr ((Relations.same _ _ _ _ _).mpr (mem_fiber.mp inside))
      rw [hb,hz] at eq
      exact (by decide : (0 : Fin 3) + 1 ≠ 2) eq

def remaining : List (List Nat) := (Routes.enumerate 16 1 16).filter fun xs => !(covered xs)

/-- Any counterexample, including one with repeated fiber sizes, has a
profile on the reported residual list. -/
theorem profile_of_counterexample {G H : Graph 16} (q : QuantumIso G H) (bad : ¬ Isomorphic G H) :
    ∃ xs ∈ remaining, Nonempty (Profile G xs) := by
  obtain ⟨xs,h,⟨P⟩⟩ := extract G
  exact ⟨xs,List.mem_filter.mpr ⟨h,by
    cases eq : covered xs with
    | false => rfl
    | true => exact (bad (isomorphic P eq q)).elim⟩,⟨P⟩⟩

theorem count : ((Routes.enumerate 16 1 16).filter covered).length = 231 := by native_decide

theorem no_remaining : remaining = [] := by native_decide

end QGI.Coherent.SixteenCoverage
