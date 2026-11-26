import LargeOrderFourFourTwelveGeometry
import LargeOrderTwelveOrbits
import LargeOrderFourDirections

noncomputable section
namespace QGI.Coherent.LargeOrderTwelvePairs
open SixTenCoordinates FourTwelveCycle FourTwelveTypes LargeOrderFourFourTwelveGeometry LargeOrderPointClosure
open LargeOrderSquareInterface SmallUnion SmallFiberExtension StrategyColorLaws
open RegionalCycleExtension (emb range_emb)
open FourTwelveFunctional (source)

variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {F : Shore (source G) l I} {S : Shore (source G) r I} {Y : Shore (source G) v Twelve}
local notation "c₀" => source G

structure Matching (g : Twelve → Edge) where
  mate : Twelve → Twelve
  inv : Function.Involutive mate
  fresh : ∀ j, mate j≠j
  unique : ∀ j k, k≠j ∧ g k=g j ↔ k=mate j

theorem matching (g : Twelve → Edge) (two : ∀ e, mult g e=2) : Nonempty (Matching g) := by
  classical
  let C (j : Twelve) := Finset.univ.filter (fun t => g t=g j)
  have mem (j) : j∈C j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  have only (j) : ((C j).erase j).card=1 := by rw [Finset.card_erase_of_mem (mem j),show (C j).card=2 from two _]
  choose f hf using fun j => Finset.card_eq_one.mp (only j)
  have spec (j k) : k≠j ∧ g k=g j ↔ k=f j := by
    simpa only [C,Finset.mem_erase,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton] using
      (Iff.of_eq (congrArg (k∈·) (hf j)))
  have atMate (j) := (spec j _).mpr rfl
  exact ⟨⟨f,fun j => ((spec _ j).mp ⟨Ne.symm (atMate j).1,(atMate j).2.symm⟩).symm,fun j => (atMate j).1,spec⟩⟩

theorem follow (B : Layout F Y) (M : Matching B.col) {X : Finset (Fin n)} (closed : Closed c₀ X)
    (j : Twelve) (inside : atPoint Y j∈X) : atPoint Y (M.mate j)∈X := by
  have hit := (M.unique j _).mpr rfl
  let marker := c₀ (atPoint Y j) (atPoint Y (M.mate j))
  apply closed.one _ inside _ (fun t => t=marker)
  intro z
  constructor
  · intro h
    obtain ⟨k,rfl⟩ := (range_emb Y z).mpr ((Relations.end_colors (closure G) h).2.trans (Y _).property)
    have gram := B.gram (i:=j) (j:=k) (x:=j) (y:=M.mate j) h
    have eq : B.col j=B.col k := (edge_overlap _ _).mp (gram.trans ((edge_overlap _ _).mpr hit.2.symm))
    have diff : k≠j := by
      rintro rfl
      exact hit.1 ((emb Y).injective (Relations.diagonal (closure G) h.symm).symm)
    exact congrArg (atPoint Y) ((M.unique j k).mp ⟨diff,eq.symm⟩)
  · rintro rfl; rfl

theorem propagate (B : Layout F Y) (two : ∀ e, mult B.col e=2) {X : Finset (Fin n)} (closed : Closed c₀ X)
    (root : atPoint F 0∈X) (right : ∀ j, atPoint Y j∈X) (i : I) : atPoint F i∈X := by
  classical
  by_cases same : i=0
  · exact same ▸ root
  obtain ⟨e,he⟩ := (by native_decide : ∀ a b : I, a≠b → ∃ e : Edge, edge e={a,b}) 0 i (Ne.symm same)
  obtain ⟨j,hj⟩ := Finset.card_pos.mp ((by decide : 0<2).trans_eq (two e).symm)
  have shape := B.columns j
  rw [(Finset.mem_filter.mp hj).2,he,Finset.map_insert,Finset.map_singleton] at shape
  apply closed.two _ (right j) _ root _ (fun h => same ((emb F).injective h)) (fun t => t=B.mark)
  intro z
  have member : z∈neighbors c₀ B.mark (atPoint Y j) ↔ c₀ (atPoint Y j) z=B.mark := by simp [neighbors]
  rw [←member,shape]
  simp only [Finset.mem_insert,Finset.mem_singleton]; rfl

theorem separate (p : PerfectStrategy G H K) (B : Layout F Y) (C : Layout S Y)
    (twoB : ∀ e, mult B.col e=2) (twoC : ∀ e, mult C.col e=2) (A : Matching B.col) (D : Matching C.col)
    (each : ∀ j, A.mate j≠D.mate j)
    (uniform : ∀ i j, c₀ (atPoint F i) (atPoint S j)=c₀ (atPoint F 0) (atPoint S 0))
    (reg : Nat → Prop) (cover : ∀ z, reg (c₀ z z) → c₀ z z=l ∨ c₀ z z=r ∨ c₀ z z=v) : Realizes p reg := by
  classical
  obtain ⟨rep,gen⟩ := LargeOrderTwelveOrbits.generators A.mate D.mate A.inv D.inv A.fresh D.fresh each
  let u : Fin 5 → Fin n := ![atPoint F 0,atPoint S 0,atPoint Y (rep 0),atPoint Y (rep 1),atPoint Y (rep 2)]
  obtain ⟨w,hw⟩ := LargeOrderFiveAnchors.complete p u 0 1 2 (by decide) (by decide) (by decide)
    (LargeOrderFourDirections.uniform_forces (sourceLaws (closure G)) F S uniform (atPoint Y (rep 0)))
  apply LargeOrderPointClosure.solve p reg _ (LargeOrderPointClosure.anchors p u w hw)
  intro X sub closed
  have seed (i : Fin 5) : u i∈X := sub (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  let T := Finset.univ.filter (fun j => atPoint Y j∈X)
  have mem (j : Twelve) : j∈T ↔ atPoint Y j∈X := by simp [T]
  have present (i : Fin 3) : rep i∈T := by
    apply (mem _).mpr
    fin_cases i
    · exact seed 2
    · exact seed 3
    · exact seed 4
  have all (j) := (mem j).mp (gen T present (fun j h => (mem _).mpr (follow B A closed j ((mem j).mp h)))
    (fun j h => (mem _).mpr (follow C D closed j ((mem j).mp h))) j)
  intro z hz
  rcases cover z ((mem_vertices _ _ _).mp hz) with h|h|h
  · obtain ⟨i,rfl⟩ := (range_emb F z).mpr h
    exact propagate B twoB closed (seed 0) all i
  · obtain ⟨i,rfl⟩ := (range_emb S z).mpr h
    exact propagate C twoC closed (seed 1) all i
  · obtain ⟨j,rfl⟩ := (range_emb Y z).mpr h
    exact all j

end QGI.Coherent.LargeOrderTwelvePairs
