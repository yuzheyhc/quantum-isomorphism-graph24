import SingletonSwitch
import CoherentCoprime
import FourSixSixQuantum

noncomputable section
namespace QGI.Literature
open Coherent

/-- Schneider–Schweitzer, *An Upper Bound on the Weisfeiler-Leman
Dimension*, full version, Lemma 5.2(4), p. 18: every nonhomogeneous
interspace between two distinct fibers of size five contains a
five-edge matching. Only one of the five rows of that relation is
needed here. https://arxiv.org/pdf/2403.12581 -/
axiom schneider_schweitzer_five_matching {n : Nat} (G : Graph n) (a b : Fin n)
    (different : b ∉ fiber G a) (left : (fiber G a).card=5) (right : (fiber G b).card=5)
    (mixed : ∃ i ∈ fiber G a, ∃ j ∈ fiber G b, Relations.color (closure G) i j ≠ Relations.color (closure G) a b) :
    ∃ i ∈ fiber G a, ∃ j ∈ fiber G b, ∀ z ∈ fiber G b,
      Relations.color (closure G) i z = Relations.color (closure G) i j → z=j
end QGI.Literature

namespace QGI.Coherent.FiveFiber
open StrategyColorLaws
open FourTwelveFunctional (source fiber_eq)

private theorem sameFiber {G : Graph 16} {i j : Fin 16} (h : i ∈ fiber G j) : fiber G i = fiber G j := by
  ext z; rw [fiber_eq,fiber_eq,(fiber_eq j i).mp h]

private theorem disjoint {G : Graph 16} {i j : Fin 16} (different : j ∉ fiber G i) :
    Disjoint (fiber G i) (fiber G j) := Finset.disjoint_left.mpr fun z zi zj => different
      ((fiber_eq _ _).mpr (((fiber_eq _ _).mp zj).symm.trans ((fiber_eq _ _).mp zi)))

/-- If a five-point fiber and a ten-point fiber occur, the remaining
vertex is a singleton. Its two other fibers are handled by the degree
switching argument. -/
private theorem five_ten {G H : Graph 16} (a b : Fin 16) (s : (fiber G a).card=5)
    (t : (fiber G b).card=10) (q : QuantumIso G H) : Isomorphic G H := by
  classical
  have apart : b ∉ fiber G a := by
    intro h
    have := congrArg Finset.card (sameFiber h)
    omega
  let rem := (fiber G a ∪ fiber G b)ᶜ
  have one : rem.card=1 := by rw [show rem.card = _ from Finset.card_compl _,Finset.card_union_of_disjoint (disjoint apart),s,t]; decide
  obtain ⟨x,hx⟩ := Finset.card_eq_one.mp one
  have mem : x ∈ rem := by simp [hx]
  have outside := Finset.mem_compl.mp mem
  have incl : fiber G x ⊆ rem := by
    intro z hz
    apply Finset.mem_compl.mpr
    rintro h
    rcases Finset.mem_union.mp h with za|zb
    · exact outside (Finset.mem_union_left _ ((fiber_eq _ _).mpr
        (((fiber_eq _ _).mp hz).symm.trans ((fiber_eq _ _).mp za))))
    · exact outside (Finset.mem_union_right _ ((fiber_eq _ _).mpr
        (((fiber_eq _ _).mp hz).symm.trans ((fiber_eq _ _).mp zb))))
  have low := Finset.card_pos.mpr ⟨x,(fiber_eq (G := G) x x).mpr rfl⟩
  have bound := Finset.card_le_card incl
  exact SingletonSwitch.isomorphic_of_three_sizes x a b (by omega) (by omega) (by omega) (by omega) q

/-- Every sixteen-point graph whose coherent closure has a fiber of
size five is determined up to isomorphism by its commuting quantum
isomorphism class. -/
theorem isomorphic_of_five {G H : Graph 16} (a : Fin 16) (five : (fiber G a).card=5)
    (q : QuantumIso G H) : Isomorphic G H := by
  classical
  let c := source G
  by_cases ten : ∃ b, (fiber G b).card = 10
  · obtain ⟨b,hb⟩ := ten
    exact five_ten a b five hb q
  by_cases uniform : ∀ b, b ∉ fiber G a → ∀ i ∈ fiber G a, ∀ j ∈ fiber G b, c i j = c a b
  · let region := fun k => k=c a a
    have left : SmallUnion.vertices c region = fiber G a := by ext z; exact (SmallUnion.mem_vertices _ _ _).trans (fiber_eq _ _).symm
    have right : SmallUnion.vertices c (fun k => ¬region k) = (fiber G a)ᶜ := by
      ext z; rw [SmallUnion.mem_vertices,Finset.mem_compl,fiber_eq]
    apply FourSixSix.isomorphic_of_uniform_cut region (by rw [left,five]; decide) (by rw [left,five]; decide)
      (by rw [right,Finset.card_compl,five]; decide) (by rw [right,Finset.card_compl,five]; decide) _ q
    intro i j x y hi hj hx hy
    have hout : j ∉ fiber G a := mt (fiber_eq _ _).mp hj
    have h := (uniform j hout i ((fiber_eq _ _).mpr hi) j ((fiber_eq _ _).mpr rfl)).trans
      (uniform j hout x ((fiber_eq _ _).mpr (hx.symm.trans hi)) y ((fiber_eq _ _).mpr hy.symm)).symm
    have eq := (Relations.same (closure G) _ _ _ _).mp h (Intertwiner.adjacency G) (adjacency_mem G)
    cases e : G.edge i j <;> cases f : G.edge x y <;> first | rfl | simp [Intertwiner.adjacency,e,f] at eq
  push_neg at uniform
  obtain ⟨b,diff,i,ha,j,hb,mixed⟩ := uniform
  have uncoprime : ¬ Nat.Coprime 5 (fiber G b).card := fun h => mixed
    (CoprimeFibers.monochromatic G a b (five ▸ h) ha hb)
  have bound := Finset.card_le_univ (fiber G a ∪ fiber G b)
  rw [Finset.card_union_of_disjoint (disjoint diff),five] at bound
  change 5 + _ ≤ 16 at bound
  have pos := Finset.card_pos.mpr ⟨b,(fiber_eq (G := G) b b).mpr rfl⟩
  have arithmetic : ∀ k : Fin 12, ¬ Nat.Coprime 5 k.val → k.val≠0 → k.val≠10 → k.val=5 := by decide
  have fiveB : (fiber G b).card=5 := arithmetic ⟨(fiber G b).card,by omega⟩ uncoprime (Nat.ne_of_gt pos) (fun h => ten ⟨b,h⟩)
  obtain ⟨u,hu,w,hw,single⟩ := Literature.schneider_schweitzer_five_matching G a b diff five fiveB ⟨i,ha,j,hb,mixed⟩
  have outside : u ∉ fiber G w := by
    rw [sameFiber hw]
    exact fun h => (Finset.disjoint_left.mp (disjoint diff)) hu h
  apply FourSixSix.isomorphic_of_thin u w outside (by rw [sameFiber hw,fiveB]; decide)
    (by rw [sameFiber hw,fiveB]; decide) _ q
  intro z eq
  have dz := (Relations.end_colors (closure G) eq).2
  exact single z ((fiber_eq _ _).mpr (dz.trans ((fiber_eq _ _).mp hw))) eq

end QGI.Coherent.FiveFiber

