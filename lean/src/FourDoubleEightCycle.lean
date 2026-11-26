import RegionalCycleExtension
import RegionalDoubleEight
import RegionalFourSixEight

noncomputable section
namespace QGI.Coherent.FourDoubleEightCycle
open FourEightGeometry FourTwelveCycle SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open LargeFourteenRegion (large)
open private twins reverse from RegionalFourFourEight

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)

def circular {l r : Nat} (F : Shore (source G) l L) (Y : Shore (source G) r Eight) := ∃ v w,
  (∀ i j, source G (atPoint F i) (atPoint Y j)=v ∨ source G (atPoint F i) (atPoint Y j)=w) ∧
  ∃ b : Eight → Edge, (∀ i j, source G (atPoint F i) (atPoint Y j)=v ↔ i∈edge (b j)) ∧ Nonempty (RepeatedCycle b)

theorem two_cycles {l r v : Nat} (F : Shore (source G) l L) (X : Shore (source G) r Eight) (Y : Shore (source G) v Eight)
    (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=v)
    (cx : circular F X) (cy : circular F Y) : Realizes p reg := by
  obtain ⟨v₁,_,_,b,mark,⟨C⟩⟩ := cx
  obtain ⟨v₂,_,_,b',mark',⟨C'⟩⟩ := cy
  have mixed : ∃ i j, source G (atPoint F i) (atPoint F j)≠source G (atPoint F 0) (atPoint F 0) :=
    ⟨0,1,fun h => (by decide : (0 : L)≠1) (F.injective (Subtype.ext (Relations.diagonal _ h)))⟩
  apply LargeOrderBlocks.of_solver p reg active rfl
  intro f g data
  apply RegionalCycleSupport.solve_patterns p data F X v₁ b mark C
  intro j
  rcases cover (f j) ((data.src _).mp ⟨j,rfl⟩) with h|h|h
  · exact FourEightMixed.patterns_at F F X (f j) (Or.inl h) mixed v₁ b mark C
  · exact FourEightMixed.patterns_at F F X (f j) (Or.inr (Or.inr (Or.inl h))) mixed v₁ b mark C
  · exact FourEightMixed.patterns_at F F Y (f j) (Or.inr (Or.inr (Or.inl h))) mixed v₂ b' mark' C'

/-- A failure for four plus two eights must have one cycle and one nonuniform
twin interface. The two eight-point fibers must also fail the twin condition. -/
theorem reduce {l r v : Nat} (lr : l≠r) (lv : l≠v) (rv : r≠v)
    (F : Shore (source G) l L) (X : Shore (source G) r Eight) (Y : Shore (source G) v Eight)
    (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=v)
    (failed : ¬Realizes p reg) :
    ¬FiberPairExtension.twins (source G) r v ∧
    ((circular F X ∧ FiberPairExtension.twins (source G) l v ∧ ¬∀ i j, source G (atPoint F i) (atPoint Y j)=source G (atPoint F 0) (atPoint Y 0)) ∨
    (circular F Y ∧ FiberPairExtension.twins (source G) l r ∧ ¬∀ i j, source G (atPoint F i) (atPoint X j)=source G (atPoint F 0) (atPoint X 0))) := by
  classical
  let c := source G
  have eights := RegionalDoubleEight.realize p (fun t => t=r ∨ t=v) (RegionalFourSixEight.pair_card rv X Y) (fun i h => by
    have same {d} (Z : Shore c d Eight) (tag : c i i=d) : (fiber G i).card=8 := by
      have seteq : fiber G i=vertices c (·=d) := by ext z; rw [FourTwelveFunctional.fiber_eq,mem_vertices]; change (c z z=c i i ↔ c z z=d); rw [tag]
      rw [seteq]; exact RegionalTwoAnchor.card Z
    exact h.elim (same X) (same Y))
  have useThin {s} (Z : Shore c s Eight) (inside : s=r ∨ s=v)
      (t : ∃ i j, ∀ z, c (atPoint Z j) z=c (atPoint Z j) (atPoint F i) → z=atPoint F i) : False := by
    obtain ⟨i,j,thin⟩ := t
    exact failed (RegionalFourFourEight.functional p eights (fun z h => (cover z h).symm)
      (atPoint Z j) (atPoint F i) ((congrArg (fun t => t=r ∨ t=v) (Z j).property).mpr inside) (F i).property thin)
  have oneCase {s t} (ls : l≠s) (lt : l≠t) (S : Shore c s Eight) (Z : Shore c t Eight)
      (cv : ∀ i, reg (c i i) → c i i=l ∨ c i i=s ∨ c i i=t)
      (old : Realizes p (fun u => u=s ∨ u=t)) (strong : circular F Z) (shape : FiberPairExtension.twins c l s) :
      (¬FiberPairExtension.twins c s t) ∧ ¬∀ i j, c (atPoint F i) (atPoint S j)=c (atPoint F 0) (atPoint S 0) := by
    constructor
    · intro twinST
      have pair := LargeOrderBlocks.small p (fun u => u=l ∨ u=t) ((RegionalTwoAnchor.pair_bound F Z).trans (by decide))
      exact failed (RegionalFourFourEight.centered p S F Z (by decide) pair (fun i h => by rcases cv i h with h|h|h <;> tauto) (reverse shape) twinST)
    · intro un
      obtain ⟨a,b,pal,edges,cells,⟨C⟩⟩ := strong
      apply failed (RegionalCycleExtension.attach p ls lt F Z (atPoint S 0) (S 0).property reg cv old ?_ a b pal edges cells C)
      intro i j hj
      simpa only [atPoint,Equiv.apply_symm_apply] using un i (S.symm ⟨j,hj⟩)
  rcases FourEightGeometry.interface F X with thin|sx|cx
  · exact (useThin X (Or.inl rfl) thin).elim
  · rcases FourEightGeometry.interface F Y with thin|sy|cy
    · exact (useThin Y (Or.inr rfl) thin).elim
    · exact (failed (RegionalFourFourEight.centered p F X Y (by decide) eights cover (twins F X sx) (twins F Y sy))).elim
    · have h := oneCase lr lv X Y cover eights cy (twins F X sx)
      exact ⟨h.1,Or.inr ⟨cy,twins F X sx,h.2⟩⟩
  · rcases FourEightGeometry.interface F Y with thin|sy|cy
    · exact (useThin Y (Or.inr rfl) thin).elim
    · have old : Realizes p (fun t => t=v ∨ t=r) := RegionalFourFourEight.restrict_map p eights (fun _ h => Or.symm h)
      have h := oneCase lv lr Y X (fun j hj => (cover j hj).imp_right Or.symm) old cx (twins F Y sy)
      exact ⟨fun h' => h.1 (reverse h'),Or.inl ⟨cx,twins F Y sy,h.2⟩⟩
    · exact (failed (two_cycles p F X Y reg active cover cx cy)).elim

end QGI.Coherent.FourDoubleEightCycle
