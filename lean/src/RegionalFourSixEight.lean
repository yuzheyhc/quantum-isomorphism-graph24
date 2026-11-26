import OddHalfPartition
import RegionalFourSixEightTetra
import LargeOrderFourteen

noncomputable section
namespace QGI.Coherent.RegionalFourSixEight
open Relations StrategyColorLaws SixTenCoordinates FourEightGeometry FourTwelveCycle SmallUnion SmallFiberExtension LargeFourteenRegion
open FourTwelveFunctional (source)
open RegionalCycleExtension (emb range_emb)
open private twins reverse shore from RegionalFourFourEight
variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (p : PerfectStrategy G H K)

theorem pair_card {l r a b : Nat} (lr : l≠r) (F : Shore (source G) l (Fin a)) (S : Shore (source G) r (Fin b)) :
    (vertices (source G) (fun z => z=l ∨ z=r)).card=a+b := by
  have eq : vertices (source G) (fun z => z=l ∨ z=r)=vertices (source G) (·=l) ∪ vertices (source G) (·=r) := by
    ext i; simp only [mem_vertices,Finset.mem_union]
  have dj : Disjoint (vertices (source G) (·=l)) (vertices (source G) (·=r)) := Finset.disjoint_left.mpr
    (fun i hi hr => lr (((mem_vertices _ _ _).mp hi).symm.trans ((mem_vertices _ _ _).mp hr)))
  rw [eq,Finset.card_union_of_disjoint dj,RegionalTwoAnchor.card F,RegionalTwoAnchor.card S]

private theorem short_cycle {l v t : Nat} (F : Shore (source G) l L) (Y : Shore (source G) v Eight) (b : Eight → Edge)
    (cells : ∀ i j, source G (atPoint F i) (atPoint Y j)=t ↔ i∈edge (b j)) (C : RepeatedCycle b) :
    ∀ j, ∃ a d, ∀ k, (∀ i, source G (atPoint F i) (atPoint Y j)=source G (atPoint F i) (atPoint Y k)) → k=a ∨ k=d := by
  intro j
  obtain ⟨a,d,small⟩ := DegreeClassRigidity.two_labels (Finset.univ.filter (fun k => C.label k=C.label j)) 0
    (le_of_eq (C.twice _))
  refine ⟨a,d,fun k same => small k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩)⟩
  have eq : edge (b k)=edge (b j) := by ext x; rw [←cells,←cells,same x]
  have inj : Function.Injective (fun i : Fin 4 => edge (cycle i)) := by native_decide
  exact inj (Finset.map_injective _ ((C.edges k).symm.trans (eq.trans (C.edges j))))

theorem solve {l r v : Nat} (lr : l≠r) (lv : l≠v) (rv : r≠v)
    (F : Shore (source G) l L) (S : Shore (source G) r (Fin 6)) (Y : Shore (source G) v Eight)
    (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=v) : Realizes p reg := by
  classical
  let c := source G
  have coverS (i) (h : reg (c i i)) : c i i=r ∨ c i i=l ∨ c i i=v := by rcases cover i h with h|h|h <;> tauto
  have coverY (i) (h : reg (c i i)) : c i i=v ∨ c i i=l ∨ c i i=r := by rcases cover i h with h|h|h <;> tauto
  have small68 := LargeOrderBlocks.fourteen p (fun t => t=r ∨ t=v) (fun i h => by
    rcases h with h|h
    · change 3 < (vertices (source G) (fun w => w=source G i i)).card; rw [h,RegionalTwoAnchor.card S]; decide
    · change 3 < (vertices (source G) (fun w => w=source G i i)).card; rw [h,RegionalTwoAnchor.card Y]; decide)
    (pair_card rv S Y)
  have fy := LargeOrderBlocks.small p _ ((RegionalTwoAnchor.pair_bound F Y).trans (by decide))
  have fs := LargeOrderBlocks.small p _ ((RegionalTwoAnchor.pair_bound F S).trans (by decide))
  have thin (i : L) (j : Eight) (one : ∀ z, c (atPoint Y j) z=c (atPoint Y j) (atPoint F i) → z=atPoint F i) : Realizes p reg :=
    RegionalFourFourEight.functional p small68 (fun z h => Or.symm (cover z h)) (atPoint Y j) (atPoint F i)
      (Or.inr (Y j).property) (F i).property one
  have tetra (t : Nat) (map : Equiv.Perm (Fin 6))
      (inc : ∀ i j, c (atPoint F i) (atPoint S j)=t ↔ FourSixSix.incident i (map j))
      (short : ∀ j, ∃ b d, ∀ z, (∀ i, c (atPoint F i) (atPoint Y j)=c (atPoint F i) (atPoint Y z)) →
        (∀ i, c (atPoint S i) (atPoint Y j)=c (atPoint S i) (atPoint Y z)) → z=b ∨ z=d) : Realizes p reg := by
    apply LargeOrderBlocks.of_solver p reg active rfl
    intro f g D
    exact RegionalFourSixEightTetra.solve p D F S Y (fun i => cover _ ((D.src _).mp ⟨i,rfl⟩)) t map inc short
  have dispatchTwin (ts : FiberPairExtension.twins c l r) : Realizes p reg := by
    rcases FourEightGeometry.interface F Y with ⟨i,j,one⟩|other|⟨t,w,pal,b,cell,⟨C⟩⟩
    · exact thin i j one
    · exact RegionalFourFourEight.centered p F S Y (by decide) small68 cover ts (twins F Y other)
    · by_cases all : ∀ i j, c (atPoint F i) (atPoint S j)=c (atPoint F 0) (atPoint S 0)
      · apply RegionalCycleExtension.attach p lr lv F Y (atPoint S 0) (S 0).property reg cover small68 _ t w pal b cell C
        intro i x hx
        simpa only [atPoint,Equiv.apply_symm_apply] using all i (S.symm ⟨x,hx⟩)
      · exact RegionalFourFourEight.centered p S F Y (by decide) fy coverS (reverse ts)
          (twins S Y (OddHalfPartition.force (sourceLaws _) F S Y ts all))
  rcases FourSixSix.Interfaces.classify (sourceLaws _) F S with ⟨t,all⟩|ts|⟨t,map,inc⟩
  · apply dispatchTwin (twins F S _)
    exact ⟨fun i x _ _ j => (all i j).trans (all x j).symm,fun _ j z _ i => (all i j).trans (all i z).symm⟩
  · exact dispatchTwin ts
  · rcases FourEightGeometry.interface F Y with ⟨i,j,one⟩|other|⟨a,_,_,b,cell,⟨C⟩⟩
    · exact thin i j one
    · rcases OddHalfPartition.short_or_twins (sourceLaws _) S Y with sync|short
      · exact RegionalFourFourEight.centered p Y F S (by decide) fs coverY (reverse (twins F Y other)) (reverse (twins S Y sync))
      · apply tetra t map inc
        intro j; obtain ⟨a,b,h⟩ := short j
        exact ⟨a,b,fun k _ same => h k same⟩
    · apply tetra t map inc
      intro j; obtain ⟨a,d,h⟩ := short_cycle F Y b cell C j
      exact ⟨a,d,fun k same _ => h k same⟩

theorem realize (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (total : (vertices (source G) reg).card=18)
    (four : ∃ a, reg (source G a a) ∧ (fiber G a).card=4)
    (six : ∃ a, reg (source G a a) ∧ (fiber G a).card=6)
    (eight : ∃ a, reg (source G a a) ∧ (fiber G a).card=8) : Realizes p reg := by
  obtain ⟨a,ha,sa⟩ := four
  obtain ⟨b,hb,sb⟩ := six
  obtain ⟨y,hy,sy⟩ := eight
  obtain ⟨F⟩ := shore a sa
  obtain ⟨S⟩ := shore b sb
  obtain ⟨Y⟩ := shore y sy
  have ne (i j : Fin n) (diff : (fiber G i).card≠(fiber G j).card) : source G i i≠source G j j := by
    intro h
    apply diff <| congrArg Finset.card (show fiber G i=fiber G j by ext z; rw [FourTwelveFunctional.fiber_eq,FourTwelveFunctional.fiber_eq,h])
  have ab := ne a b (by rw [sa,sb]; decide)
  have ay := ne a y (by rw [sa,sy]; decide)
  have by' := ne b y (by rw [sb,sy]; decide)
  exact solve p ab ay by' F S Y reg active
    (RegionalFourFourEight.three_cover ha hb hy ab ay by' (by rw [sa,sb,sy,total]))

end QGI.Coherent.RegionalFourSixEight
