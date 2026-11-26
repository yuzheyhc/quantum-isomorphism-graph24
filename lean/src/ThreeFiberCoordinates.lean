import SixTenCoordinates

noncomputable section
namespace QGI.Coherent.ThreeFiberCoordinates
open Relations SixTenCoordinates

private theorem mem_color (G : Graph 16) (a x : Fin 16) :
    x ∈ fiber G a ↔ color (closure G) x x = color (closure G) a a :=
  mem_fiber.trans (same _ _ _ _ _).symm

theorem disjoint_of_sizes {G : Graph 16} {a b : Fin 16}
    (h : (fiber G a).card ≠ (fiber G b).card) : a ∉ fiber G b := by
  intro mem
  have eq := (mem_color G b a).mp mem
  exact h (congrArg Finset.card (show fiber G a = fiber G b by ext x; simp only [mem_color,eq]))

theorem frames (G : Graph 16) (a b c : Fin 16) {s t u : Nat}
    (sa : (fiber G a).card=s) (sb : (fiber G b).card=t) (sc : (fiber G c).card=u)
    (total : s+t+u=16) (ab : a∉fiber G b) (ac : a∉fiber G c) (bc : b∉fiber G c) :
    ∃ l r v, l≠r ∧ l≠v ∧ r≠v ∧
      Nonempty (Shore (color (closure G)) l (Fin s)) ∧
      Nonempty (Shore (color (closure G)) r (Fin t)) ∧
      Nonempty (Shore (color (closure G)) v (Fin u)) ∧
      ∀ x, color (closure G) x x=l ∨ color (closure G) x x=r ∨ color (closure G) x x=v := by
  classical
  let d := fun z => color (closure G) z z
  have ab' : d a ≠ d b := mt (mem_color G b a).mpr ab
  have ac' : d a ≠ d c := mt (mem_color G c a).mpr ac
  have bc' : d b ≠ d c := mt (mem_color G c b).mpr bc
  have sh (x : Fin 16) (k : Nat) (sz : (fiber G x).card=k) :
      Nonempty (Shore (color (closure G)) (d x) (Fin k)) := by
    let e := Equiv.subtypeEquivRight (fun z => mem_color G x z)
    let f := Fintype.equivOfCardEq (show Fintype.card (Fin k)=Fintype.card {z // z ∈ fiber G x} by simp [sz])
    exact ⟨f.trans e⟩
  have dj (i j : Fin 16) (ne : d i ≠ d j) : Disjoint (fiber G i) (fiber G j) :=
    Finset.disjoint_left.mpr fun z hi hj => ne (((mem_color _ _ _).mp hi).symm.trans ((mem_color _ _ _).mp hj))
  have all : (fiber G a ∪ fiber G b) ∪ fiber G c = Finset.univ :=
    Finset.eq_univ_of_card _ (by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨dj _ _ ac',dj _ _ bc'⟩),
        Finset.card_union_of_disjoint (dj _ _ ab'),sa,sb,sc]
      exact total)
  refine ⟨d a,d b,d c,ab',ac',bc',sh a s sa,sh b t sb,sh c u sc,fun x => ?_⟩
  have mem : x ∈ (fiber G a ∪ fiber G b) ∪ fiber G c := all ▸ Finset.mem_univ _
  simpa only [Finset.mem_union,mem_color,or_assoc,d] using mem

end QGI.Coherent.ThreeFiberCoordinates
