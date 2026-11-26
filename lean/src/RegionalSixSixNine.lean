import SixNineSameTriples
import SixNineTwoPartitions
import RegionalMarkPins
import SixSixEightPins

noncomputable section
namespace QGI.Coherent.RegionalSixSixNine
open SixTenCoordinates SixEightGeometry SmallUnion SmallFiberExtension LargeFourteenRegion StrategyColorLaws Intertwiner
open FourTwelveFunctional (source)
open SixSixEightPins (Flat flat_twins flip_flat)
open SixNineGridGeometry (HasFour Triple)
open RegionalShorePins (Short pinned)
open private reverse twins shore from RegionalFourFourEight

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (p : PerfectStrategy G H K)

theorem small_row {l r m} [NeZero m] (A : Shore (source G) l (Fin 6)) (B : Shore (source G) r (Fin m))
    (h : ¬Flat A B) : Short A (atPoint B) := by
  intro i
  apply (Finset.card_le_card ?_).trans (ShoreSignatureSize.half (sourceLaws _) A B h i)
  intro b hb
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hb ⊢
  exact hb

theorem solve {l r v : Nat} (lv : l≠v) (rv : r≠v)
    (A : Shore (source G) l (Fin 6)) (B : Shore (source G) r (Fin 6)) (Y : Shore (source G) v (Fin 9))
    (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=v) : Realizes p reg := by
  classical
  let c := source G
  have cv (i) (h : reg (c i i)) : c i i=r ∨ c i i=l ∨ c i i=v := by rcases cover i h with h|h|h <;> tauto
  have yc (i) (h : reg (c i i)) : c i i=v ∨ c i i=l ∨ c i i=r := by rcases cover i h with h|h|h <;> tauto
  have ab := LargeOrderBlocks.small p _ ((RegionalTwoAnchor.pair_bound A B).trans (by decide))
  have ba := RegionalFourFourEight.restrict_map p ab (t:=fun t => t=r ∨ t=l) (fun _ h => Or.symm h)
  have pair {s} (S : Shore c s (Fin 6)) (diff : s≠v) : Realizes p (fun t => t=s ∨ t=v) := by
    apply LargeOrderBlocks.of_solver p _ _ (RegionalFourSixEight.pair_card diff S Y) (Fifteen.solve p _)
    intro i hi
    change 3 < (vertices (source G) (·=source G i i)).card
    rcases hi with h|h
    · rw [h,RegionalTwoAnchor.card S]; decide
    · rw [h,RegionalTwoAnchor.card Y]; decide
  have pin (four : HasFour Y) : ∃ (ξ : Synchrony.cyclic p) (g : Fin 9 → Fin n), ξ≠0 ∧ ∀ i, U p (atPoint Y i) (g i) ξ=ξ := by
    obtain ⟨g,gi,gs,gd,gn⟩ := four
    exact RegionalMarkPins.fixed p Y (NinePointRigidity.commuting p Y g gi gs gd gn)
  have mixed (ha : ¬Flat A Y) (hb : ¬Flat B Y) (four : HasFour Y) : Realizes p reg := by
    obtain ⟨ξ,t,nz,fixed⟩ := pin four
    exact RegionalShorePins.realize p A B Y reg active cover ξ nz (atPoint Y) t fixed (small_row A Y ha) (small_row B Y hb) (pinned Y)
  have flatCase {s t} (F : Shore c s (Fin 6)) (S : Shore c t (Fin 6)) (tv : t≠v)
      (old : Realizes p (fun u => u=s ∨ u=t)) (cross : Flat F Y)
      (cov : ∀ i, reg (c i i) → c i i=s ∨ c i i=t ∨ c i i=v)
      (sm : ¬Flat S Y) : Realizes p reg := by
    have alt := (SixNineGridGeometry.classify tv S Y).resolve_left sm
    rcases alt with pack|⟨g,different⟩
    · obtain ⟨P⟩ := pack
      apply SixNineAttachments.attach p F S Y reg cov _ old P.mark P.a P.b _ _ P.flag P.uniform
      · intro x y hx hy
        obtain ⟨i,hi⟩ := (RegionalCycleExtension.range_emb F x).mpr hx
        obtain ⟨j,hj⟩ := (RegionalCycleExtension.range_emb Y y).mpr hy
        simpa only [←hi,←hj] using cross i j
      · intro x; obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter (fun i => P.a i=x)).card by rw [P.aSize]; decide)
        exact ⟨i,(Finset.mem_filter.mp hi).2⟩
      · intro x; obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter (fun i => P.b i=x)).card by rw [P.bSize]; decide)
        exact ⟨i,(Finset.mem_filter.mp hi).2⟩
    · by_cases fs : Flat F S
      · exact RegionalFourFourEight.centered p F S Y (by decide) (pair S tv) cov (twins F S (flat_twins F S fs)) (twins F Y (flat_twins F Y cross))
      obtain ⟨ξ,tg,nz,fy⟩ := pin g
      obtain ⟨sg,fS⟩ := RegionalMarkPins.grow p nz (atPoint Y) tg fy S (fun i b h => (different b i h))
      let k := Sum.elim (atPoint S) (atPoint Y)
      have hh : ∀ j, U p (k j) (Sum.elim sg tg j) ξ=ξ := by rintro (i|j); exact fS i; exact fy j
      have ss (i) : ∃ j, k j=atPoint S i := ⟨Sum.inl i,rfl⟩
      have ys (i) : ∃ j, k j=atPoint Y i := ⟨Sum.inr i,rfl⟩
      exact RegionalShorePins.realize p F S Y reg active cov ξ nz k _ hh
        (RegionalMarkPins.widen F (small_row F S fs) ss) (RegionalMarkPins.widen S (pinned S) ss) (RegionalMarkPins.widen Y (pinned Y) ys)
  by_cases af : Flat A Y
  · by_cases bf : Flat B Y
    · exact RegionalFourFourEight.centered p Y A B (by decide) ab yc (reverse (twins A Y (flat_twins A Y af))) (reverse (twins B Y (flat_twins B Y bf)))
    · exact flatCase A B rv ab af cover bf
  by_cases bf : Flat B Y
  · exact flatCase B A lv ba bf cv af
  have first := (SixNineGridGeometry.classify lv A Y).resolve_left af
  rcases first with pa|⟨g,_⟩
  · obtain ⟨P⟩ := pa
    have second := (SixNineGridGeometry.classify rv B Y).resolve_left bf
    rcases second with pb|⟨g,_⟩
    · obtain ⟨Q⟩ := pb
      rcases SixNineTwoPartitions.alternative P Q with same|g
      · exact SixNineSameTriples.attach p A B Y P Q same reg cover ba
      · exact mixed af bf g
    · exact mixed af bf g
  · exact mixed af bf g

theorem realize (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (total : (vertices (source G) reg).card=21)
    (nine : ∃ y, reg (source G y y) ∧ (fiber G y).card=9)
    (sixes : ∃ a b, reg (source G a a) ∧ reg (source G b b) ∧ (fiber G a).card=6 ∧ (fiber G b).card=6 ∧ source G a a≠source G b b) :
    Realizes p reg := by
  obtain ⟨y,hy,sy⟩ := nine
  obtain ⟨a,b,ha,hb,sa,sb,ab⟩ := sixes
  obtain ⟨A⟩ := shore a sa; obtain ⟨B⟩ := shore b sb; obtain ⟨Y⟩ := shore y sy
  have diff (x : Fin n) (sx : (fiber G x).card=6) : source G x x≠source G y y := by
    intro eq
    have same : fiber G x=fiber G y := by ext i; rw [FourTwelveFunctional.fiber_eq,FourTwelveFunctional.fiber_eq,eq]
    rw [same,sy] at sx
    contradiction
  exact solve p (diff a sa) (diff b sb) A B Y reg active
    (RegionalFourFourEight.three_cover ha hb hy ab (diff a sa) (diff b sb) (by rw [sa,sb,sy,total]))

end QGI.Coherent.RegionalSixSixNine
