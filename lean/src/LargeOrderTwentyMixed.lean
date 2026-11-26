import LargeOrderSixTenInterface
import LargeOrderSixteenShapes

noncomputable section
namespace QGI.Coherent.LargeOrderTwentyMixed
open SmallUnion SmallFiberExtension LargeFourteenRegion SixTenCoordinates
open FourTwelveFunctional (source fiber_eq)
open private reverse shore from RegionalFourFourEight
variable {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

theorem realize (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (size : (vertices (source G) reg).card=20)
    (four : ∃ x, reg (source G x x) ∧ (fiber G x).card=4)
    (six : ∃ x, reg (source G x x) ∧ (fiber G x).card=6)
    (ten : ∃ x, reg (source G x x) ∧ (fiber G x).card=10) : Realizes p reg := by
  let c := source G
  obtain ⟨a,ha,sa⟩ := four
  obtain ⟨b,hb,sb⟩ := six
  obtain ⟨t,ht,st⟩ := ten
  obtain ⟨F⟩ := shore a sa
  obtain ⟨S⟩ := shore b sb
  obtain ⟨Y⟩ := shore t st
  have diff (i j : Fin n) (h : (fiber G i).card≠(fiber G j).card) : c i i≠c j j := by
    intro eq
    change source G i i=source G j j at eq
    exact h (congrArg Finset.card (show fiber G i=fiber G j by ext x; simp only [fiber_eq,←eq]))
  have ab := diff a b (by rw [sa,sb]; decide)
  have at' := diff a t (by rw [sa,st]; decide)
  have bt := diff b t (by rw [sb,st]; decide)
  have cover := RegionalFourFourEight.three_cover ha hb ht ab at' bt (by rw [sa,sb,st,size])
  have card (i j : Fin n) (ne : c i i≠c j j) :
      (vertices c (fun k => k=c i i ∨ k=c j j)).card=(fiber G i).card+(fiber G j).card := by
    have eq : vertices c (fun k => k=c i i ∨ k=c j j)=fiber G i ∪ fiber G j := by ext z; simp [c,fiber_eq]
    rw [eq,Finset.card_union_of_disjoint (Finset.disjoint_left.mpr
      (fun z hi hj => ne (((fiber_eq _ _).mp hi).symm.trans ((fiber_eq _ _).mp hj))))]
  have ft := FourByEven.rectangle (sourceLaws (closure G)) F Y (Or.inl rfl)
  rcases LargeOrderSquareInterface.four_six (sourceLaws (closure G)) F S with fs|tetra
  · let old := fun k => k=c b b ∨ k=c t t
    have active' (x : Fin n) (h : old (c x x)) : large G (c x x) := by
      apply active
      rcases h with h|h
      · change reg (c x x); rw [h]; exact hb
      · change reg (c x x); rw [h]; exact ht
    apply RegionalFourFourEight.centered p F S Y (by decide) _ cover fs ft
    apply RegionalSixTen.realize p old active'
    · rw [show (vertices c old).card=_ from card b t bt,sb,st]
    · exact ⟨b,Or.inl rfl,sb⟩
    · exact ⟨t,Or.inr rfl,st⟩
  · rcases LargeOrderSixTenInterface.classify (sourceLaws (closure G)) S Y with sy|dsg
    · apply RegionalFourFourEight.centered p Y F S (by decide) _
        (fun i h => by rcases cover i h with a|a|a <;> tauto) (reverse ft) (reverse sy)
      apply LargeOrderBlocks.small
      rw [card a b ab,sa,sb]; decide
    · exact (LargeOrderSixTenInterface.incompatible (sourceLaws (closure G)) tetra dsg).elim

end QGI.Coherent.LargeOrderTwentyMixed
