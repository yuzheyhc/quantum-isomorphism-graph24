import Orders.Order17
import FivePointProfiles
import RegionalEightFourteen
import RegionalSixExterior
import RegionalFourSixTwelve

namespace QGI.Coherent.ProfileCoverage
open CoprimeProfiles

def covered (n : Nat) (xs : List Nat) : Bool :=
  decide (n≤17) || FivePointProfiles.covered xs || xs == [n] || decide (8∈xs ∧ 14∈xs) || RegionalSixExterior.accepted xs ||
    decide ((xs.filter (fun k => 3<k)).sum=22 ∧ 4∈xs ∧ 6∈xs ∧ 12∈xs)

theorem isomorphic {n : Nat} (lo : 16 ≤ n) (hi : n ≤ 23) {G H : Graph n} {xs : List Nat}
    (P : Profile G xs) (yes : covered n xs = true) (q : QuantumIso G H) : Isomorphic G H := by
  simp only [covered,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at yes
  rcases yes with ((((lower | blocks) | rfl) | pair) | outside) | last
  · rcases (show n=16 ∨ n=17 by omega) with rfl | rfl
    · exact noSeparation16 G H q
    · exact noSeparation17 G H q
  · exact FivePointProfiles.isomorphicWith (LargeOrderProfiles.boundedNineteen (by omega)) P blocks q
  · by_contra bad
    obtain ⟨i,_,lt⟩ := counterexample_has_proper_large_fiber lo hi q bad
    have ht : P.tag i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    have sz : (fiber G i).card=n := by rw [P.fiber_size,ht]; rfl
    omega
  · obtain ⟨K,ng,ip,c,⟨p⟩⟩ := q
    letI : NormedAddCommGroup K := ng
    letI : InnerProductSpace ℂ K := ip
    letI : CompleteSpace K := c
    have occurs (v : Nat) (pos : 0<v) (hv : v∈xs) : ∃ i, (fiber G i).card=v := by
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp hv
      obtain ⟨i,hi⟩ := P.occurs j (by change 0<xs.get j; rw [hj]; exact pos)
      refine ⟨i,?_⟩; rw [P.fiber_size,hi]; exact hj
    exact RegionalEightFourteen.isomorphic p hi (occurs 8 (by decide) pair.1) (occurs 14 (by decide) pair.2)
  · exact RegionalSixExterior.by_profile hi P outside q
  · exact RegionalFourSixTwelve.isomorphic P last.1 last.2.1 last.2.2.1 last.2.2.2 q

def tally (n : Nat) := ((Routes.enumerate n 1 n).filter (covered n)).length

def residual (n : Nat) := (Routes.enumerate n 1 n).filter (fun s => !(covered n s))

set_option maxRecDepth 10000 in
theorem counted_at_least :
    List.Forall₂ (·≤·) [231,297,384,489,617,776,964,1200] ((List.range 8).map (fun i => tally (16+i))) := by
  native_decide

set_option maxRecDepth 10000 in
/-- Exact number of fiber-size partitions handled by this classifier at each order. -/
theorem exact_counts :
    (List.range 8).map (fun i => tally (16+i)) = [231,297,385,490,627,792,1002,1255] := by
  native_decide

set_option maxRecDepth 10000 in
/-- All fiber-size profiles at the eight requested orders have a verified route. -/
theorem all_covered : ∀ i : Fin 8, residual (16+i.val)=[] := by native_decide

def residualCores : List (List Nat) := []

set_option maxRecDepth 10000 in
theorem remaining_core_list : ∀ i : Fin 4,
    (residual (20+i.val)).all (fun xs => residualCores.contains (xs.filter (fun k => 3<k))) = true := by
  native_decide

theorem profile_of_counterexample {n} (lo : 16 ≤ n) (hi : n ≤ 23) {G H : Graph n}
    (q : QuantumIso G H) (bad : ¬ Isomorphic G H) :
    ∃ xs ∈ (Routes.enumerate n 1 n).filter (fun s => !(covered n s)), Nonempty (Profile G xs) := by
  obtain ⟨xs,h,⟨P⟩⟩ := extract G
  exact ⟨xs,List.mem_filter.mpr ⟨h,by
    cases eq : covered n xs with
    | false => rfl
    | true => exact (bad (isomorphic lo hi P eq q)).elim⟩,⟨P⟩⟩

end QGI.Coherent.ProfileCoverage
