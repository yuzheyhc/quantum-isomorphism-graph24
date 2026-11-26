import FourPointGeneral
import RegionalFourSixEight
import LargeOrderSingle
import NineNineRectangles

noncomputable section
namespace QGI.Coherent.FourSixteenRegion
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source fiber_eq)
open RegionalCycleExtension (emb range_emb)
open private shore twins from RegionalFourFourEight

private def cell {n : Nat} (c : Table n) (l : Nat) : ThreeRectangleExtension.Cell c l ≃ {i // c i i=l} :=
  Equiv.subtypeEquivRight (fun i => mem_vertices _ _ i)

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

/-- When six does not divide the opposite shore, any named realization on that shore
extends across four points. This also applies inside a larger graph. -/
theorem extend_cases {m l r : Nat} [NeZero m] (F : Shore (source G) l (Fin 4))
    (Y : Shore (source G) r (Fin m)) (old : Realizes p (·=r))
    (cases : (∃ i j, ∀ z, source G (atPoint Y j) z=source G (atPoint Y j) (atPoint F i) → z=atPoint F i) ∨
      SplitRectangle.Twins (fun i j => source G (atPoint F i) (atPoint Y j)) ∨
      ∃ v w, (∀ i j, source G (atPoint F i) (atPoint Y j)=v ∨ source G (atPoint F i) (atPoint Y j)=w) ∧
        ∃ b : Fin m → FourTwelveCycle.Edge, (∀ i j, source G (atPoint F i) (atPoint Y j)=v ↔ i∈FourTwelveCycle.edge (b j)) ∧ Nonempty (FourPointGeneral.Cycle b)) :
    Realizes p (fun t => t=r ∨ t=l) := by
  classical
  let c := source G
  let d := targetName p
  rcases cases with ⟨i,j,thin⟩|matched|⟨v,w,pal,b,cells,⟨C⟩⟩
  · exact RegionalFourFourEight.functional p old (fun _ h => h) (atPoint Y j) (atPoint F i) (Y j).property (F i).property thin
  · let y : Region c (·=r) := ⟨atPoint Y 0,(mem_vertices _ _ _).mpr (Y 0).property⟩
    have eq : source G y.val y.val=r := (Y 0).property
    have twin := twins F Y matched
    apply FiberPairExtension.attach p F 0 (by decide) (·=r) old y y
    · intro i; exact Or.inl (((mem_vertices _ _ _).mp i.property).trans eq.symm)
    · rw [eq]; exact twin
    · rw [eq]; exact twin
  obtain ⟨e,he⟩ := old
  let L := (C.points.trans F).trans (cell c l).symm
  let W := Y.trans (cell c r).symm
  let Z := (W.trans e).toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
  obtain ⟨u,hu⟩ := diagonal_names p
  let T : Shore d l (Fin 4) := F.trans (Equiv.subtypeEquiv u (fun x => ⟨fun h => (hu x).symm.trans h,fun h => (hu x).trans h⟩))
  let sl := C.points.toEmbedding.trans (emb F)
  have rangeS (x) : x∈Set.range sl ↔ c x x=l := by
    refine Iff.trans ?_ (range_emb F x)
    exact ⟨fun ⟨i,h⟩ => ⟨C.points i,h⟩,fun ⟨i,h⟩ => ⟨C.points.symm i,by simpa [sl] using h⟩⟩
  obtain ⟨a,z,az,rows,names⟩ := FourPointGeneral.edges F Y v w pal b cells C
  obtain ⟨h,hll,hrl⟩ := RegionalFourTwelve.cycle_named p az sl (emb T) (emb Y) Z rangeS (range_emb T)
    (fun i j => he (W i) (W j)) C.label C.full rows names
  let R := (h.trans T).trans (cell d l).symm
  let g := L.symm.trans R
  have loc (i) : g (L i)=R i := by simp [g]
  apply ThreeRectangleExtension.merge_maps p (·=r) l e g he
  · intro i j; obtain ⟨i,rfl⟩ := L.surjective i; obtain ⟨j,rfl⟩ := L.surjective j
    rw [loc,loc]; exact hll i j
  · intro i j; obtain ⟨i,rfl⟩ := W.surjective i; obtain ⟨j,rfl⟩ := L.surjective j
    rw [loc]; exact hrl i j

theorem extend {m l r : Nat} [NeZero m] (nodiv : ¬6 ∣ m) (F : Shore (source G) l (Fin 4))
    (Y : Shore (source G) r (Fin m)) (old : Realizes p (·=r)) :
    Realizes p (fun t => t=r ∨ t=l) := by
  exact extend_cases p F Y old (FourPointGeneral.interface nodiv F Y)

variable [CompleteSpace K]
theorem realize (reg : Nat → Prop) (size : (vertices (source G) reg).card=20)
    (four : ∃ i, reg (source G i i) ∧ (fiber G i).card=4)
    (sixteen : ∃ i, reg (source G i i) ∧ (fiber G i).card=16) : Realizes p reg := by
  classical
  obtain ⟨a,ha,sa⟩ := four; obtain ⟨b,hb,sb⟩ := sixteen
  let c := source G
  obtain ⟨F⟩ := shore a sa; obtain ⟨Y⟩ := shore b sb
  have old := LargeOrderBlocks.of_solver p (·=c b b) (fun i h => by
      change source G i i=source G b b at h; change 3 < (vertices (source G) (·=source G i i)).card; rw [h,RegionalTwoAnchor.card Y]; decide)
    (RegionalTwoAnchor.card Y) (fun f g D => LargeOrderSingle.solve p f g D (fun i j =>
      ((D.src _).mp ⟨i,rfl⟩).trans ((D.src _).mp ⟨j,rfl⟩).symm))
  have ne : c b b≠c a a := by
    intro eq
    have same : fiber G b=fiber G a := by ext z; rw [fiber_eq,fiber_eq]; change (c z z=c b b ↔ c z z=c a a); rw [eq]
    have h := congrArg Finset.card same; omega
  let R := fun t => t=c b b ∨ t=c a a
  have all : vertices c R=vertices c reg := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi; apply (mem_vertices _ _ _).mpr
      rcases (mem_vertices _ _ _).mp hi with h|h
      · exact h.symm ▸ hb
      · exact h.symm ▸ ha
    · rw [size,RegionalFourSixEight.pair_card ne Y F]
  apply RegionalFourFourEight.restrict_map p (extend p (by decide : ¬6 ∣ 16) F Y old)
  intro i hi
  apply (mem_vertices c R i).mp
  rw [all]; exact (mem_vertices _ _ _).mpr hi

end QGI.Coherent.FourSixteenRegion
