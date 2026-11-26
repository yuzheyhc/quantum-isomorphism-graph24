import LargeOrderFourSixSix
import RegionalFourFourEight
import RegionalFourTwelve

namespace QGI.Coherent.LargeOrderSixteenShapes
open CoprimeProfiles SmallUnion LargeFourteenRegion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)

abbrev Has {xs : List Nat} (ids : Finset (Fin xs.length)) (k : Nat) :=
  ∃ i ∈ ids, xs[i.val]=k

abbrev Twice {xs : List Nat} (ids : Finset (Fin xs.length)) (k : Nat) :=
  ∃ i ∈ ids, ∃ j ∈ ids, i≠j ∧ xs[i.val]=k ∧ xs[j.val]=k

def recognized {xs : List Nat} (ids : Finset (Fin xs.length)) :=
  decide ((Has ids 4 ∧ Has ids 12) ∨ (Has ids 8 ∧ Twice ids 4) ∨ (Has ids 4 ∧ Twice ids 6))

theorem single {n k : Nat} {G : Graph n} {xs : List Nat} (P : Profile G xs) {ids : Finset (Fin xs.length)}
    {reg : Nat → Prop} (shape : ∀ i, reg (source G i i) ↔ P.tag i ∈ ids) (pos : 0<k) (h : Has ids k) :
    ∃ i, reg (source G i i) ∧ (fiber G i).card=k := by
  obtain ⟨i,hi,hk⟩ := h
  obtain ⟨x,hx⟩ := P.occurs i (hk.symm ▸ pos)
  exact ⟨x,(shape _).mpr (hx.symm ▸ hi),by rw [P.fiber_size,hx,hk]⟩

theorem two {n k : Nat} {G : Graph n} {xs : List Nat} (P : Profile G xs) {ids : Finset (Fin xs.length)}
    {reg : Nat → Prop} (shape : ∀ i, reg (source G i i) ↔ P.tag i ∈ ids) (pos : 0<k) (h : Twice ids k) :
    ∃ x y, reg (source G x x) ∧ reg (source G y y) ∧ (fiber G x).card=k ∧ (fiber G y).card=k ∧
      source G x x≠source G y y := by
  obtain ⟨i,hi,j,hj,ne,hk,hl⟩ := h
  obtain ⟨x,hx⟩ := P.occurs i (hk.symm ▸ pos)
  obtain ⟨y,hy⟩ := P.occurs j (hl.symm ▸ pos)
  exact ⟨x,y,(shape _).mpr (hx.symm ▸ hi),(shape _).mpr (hy.symm ▸ hj),
    by rw [P.fiber_size,hx,hk],by rw [P.fiber_size,hy,hl],
    fun eq => ne (hx.symm.trans (((P.same _ _).mpr eq).trans hy))⟩

theorem solve {n : Nat} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)
    {ids : Finset (Fin xs.length)} {reg : Nat → Prop} (shape : ∀ i, reg (source G i i) ↔ P.tag i ∈ ids)
    (active : ∀ i, reg (source G i i) → large G (source G i i)) (size : (vertices (source G) reg).card=16)
    (ok : recognized ids=true) : Realizes p reg := by
  rcases of_decide_eq_true ok with ⟨four,twelve⟩ | ⟨eight,fours⟩ | ⟨four,sixes⟩
  · exact RegionalFourTwelve.realize p reg active size (single P shape (by decide) four) (single P shape (by decide) twelve)
  · exact RegionalFourFourEight.realize p reg active size (single P shape (by decide) eight) (two P shape (by decide) fours)
  · exact LargeOrderFourSixSix.realize p reg active size (single P shape (by decide) four) (two P shape (by decide) sixes)

end QGI.Coherent.LargeOrderSixteenShapes
