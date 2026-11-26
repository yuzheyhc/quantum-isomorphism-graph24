import FourHalfGlue

noncomputable section
namespace QGI.Coherent.RegionalFourEightEight
open QGI.FourHalfCatalog (Four Eight)
open SixTenCoordinates FourHalfModel SmallUnion SmallFiberExtension StrategyColorLaws LargeFourteenRegion
open FourTwelveFunctional (source)
open private reverse shore from RegionalFourFourEight

variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
   (p : PerfectStrategy G H K)

private theorem pair (X : Shore (source G) r Eight) (Y : Shore (source G) v Eight) (rv : r≠v) :
    Realizes p (fun t => t=r ∨ t=v) := by
  apply RegionalDoubleEight.realize p _ (RegionalFourSixEight.pair_card rv X Y)
  intro i h
  have size {d} (Z : Shore (source G) d Eight) (tag : source G i i=d) : (fiber G i).card=8 := by
    have eq : fiber G i=vertices (source G) (·=d) := by
      ext z; rw [FourTwelveFunctional.fiber_eq,mem_vertices,tag]
    rw [eq,RegionalTwoAnchor.card Z]
  exact h.elim (size X) (size Y)

private theorem on_chart (F : Shore (source G) l Four) (P : Chart (source G) r v)
    (lr : l≠r) (lv : l≠v) (rv : r≠v) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=v)
    (cy : FourDoubleEightCycle.circular F P.X) (tw : FiberPairExtension.twins (source G) l v)
    (nt : ¬FiberPairExtension.twins (source G) r v)
    (nf : ¬∀ i j, source G (atPoint F i) (atPoint P.Y j)=source G (atPoint F 0) (atPoint P.Y 0)) :
    Realizes p reg := by
  let c := source G
  have old := pair p P.X P.Y rv
  obtain ⟨TX,TY,keep⟩ := targets p P.X P.Y old
  obtain ⟨q,bal,⟨D⟩⟩ := align p F P.X TX (fun i j => keep (.inl i) (.inl j)) cy
  obtain ⟨q',bal',can,⟨D'⟩⟩ := normalize p bal D
  rcases FourPointGeneral.interface_detailed D'.F P.Y with thin|flat|⟨a,z,_,two,b,mark,_⟩
  · obtain ⟨i,j,h⟩ := thin
    exact RegionalFourFourEight.functional p old (fun i hi => (cover i hi).symm)
      (atPoint P.Y j) (atPoint D'.F i) (Or.inr (P.Y j).property) (D'.F i).property h
  · exfalso; apply nf
    intro i j
    let whereF (k : Four) := D'.F.symm (F k)
    have loc (k : Four) : atPoint D'.F (whereF k)=atPoint F k := congrArg Subtype.val (D'.F.apply_symm_apply _)
    simpa only [loc] using (flat (whereF i) j).trans (flat (whereF 0) 0).symm
  · exact RegionalFourFourEight.restrict_map p (glue p P D' lr lv rv bal' can keep nt tw a z two b mark) cover

theorem solve (F : Shore (source G) l Four) (X : Shore (source G) r Eight) (Y : Shore (source G) v Eight)
    (lr : l≠r) (lv : l≠v) (rv : r≠v) (reg : Nat → Prop)
    (active : ∀ i, reg (source G i i) → large G (source G i i))
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=v) : Realizes p reg := by
  rcases represent X Y rv with ⟨i,j,thin⟩|⟨P⟩
  · have old := LargeOrderBlocks.small p _ ((RegionalTwoAnchor.pair_bound F X).trans (by decide))
    exact RegionalFourFourEight.functional p old (fun i hi => by rcases cover i hi with h|h|h <;> tauto)
      (atPoint X i) (atPoint Y j) (Or.inr (X i).property) (Y j).property thin
  · obtain ⟨P⟩ := P
    by_contra failed
    obtain ⟨nt,cases⟩ := FourDoubleEightCycle.reduce p lr lv rv F P.X P.Y reg active cover failed
    rcases cases with ⟨cy,tw,flat⟩|⟨cy,tw,flat⟩
    · exact failed (on_chart p F P lr lv rv reg cover cy tw nt flat)
    · exact failed (on_chart p F P.flip lv lr (Ne.symm rv) reg (fun i h => (cover i h).imp_right Or.symm)
        cy tw (fun h => nt (reverse h)) flat)

theorem realize (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (total : (vertices (source G) reg).card=20)
    (four : ∃ y, reg (source G y y) ∧ (fiber G y).card=4)
    (eights : ∃ a b, reg (source G a a) ∧ reg (source G b b) ∧ (fiber G a).card=8 ∧ (fiber G b).card=8 ∧ source G a a≠source G b b) :
    Realizes p reg := by
  obtain ⟨y,hy,sy⟩ := four
  obtain ⟨a,b,ha,hb,sa,sb,ab⟩ := eights
  obtain ⟨F⟩ := shore y sy; obtain ⟨X⟩ := shore a sa; obtain ⟨Y⟩ := shore b sb
  have diff (x : Fin n) (sx : (fiber G x).card=8) : source G y y≠source G x x := by
    intro eq
    have same : fiber G y=fiber G x := by ext i; rw [FourTwelveFunctional.fiber_eq,FourTwelveFunctional.fiber_eq,eq]
    rw [same,sx] at sy
    contradiction
  exact solve p F X Y (diff a sa) (diff b sb) ab reg active
    (RegionalFourFourEight.three_cover hy ha hb (diff a sa) (diff b sb) ab (by rw [sy,sa,sb,total]))

end QGI.Coherent.RegionalFourEightEight
