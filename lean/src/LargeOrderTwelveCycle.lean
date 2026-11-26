import LargeOrderFourFourTwelveGeometry
import RegionalFourSixEight

noncomputable section
namespace QGI.Coherent.LargeOrderTwelveCycle
open SixTenCoordinates LargeOrderFourFourTwelveGeometry FourTwelveCycle LargeOrderSquareInterface
open SmallUnion SmallFiberExtension FiberPairExtension StrategyColorLaws LargeFourteenRegion
open RegionalCycleExtension (emb range_emb)
open FourTwelveFunctional (source)

variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)
local notation "c₀" => source G

private theorem card {k s : Nat} (F : Shore c₀ s (Fin k)) (i) : (fiber G (atPoint F i)).card=k := by
  have set : fiber G (atPoint F i)=vertices c₀ (·=s) := by ext z; simp only [FourTwelveFunctional.fiber_eq,mem_vertices,(F i).property]
  rw [set,RegionalTwoAnchor.card F]

theorem pair (F : Shore c₀ l I) (Y : Shore c₀ v Twelve) (apart : l≠v) : Realizes p (fun t => t=l ∨ t=v) := by
  apply RegionalFourTwelve.realize p
  · intro x hx
    apply (LargeOrderBlocks.large_iff _).mpr
    rcases hx with h|h
    · obtain ⟨i,rfl⟩ := (range_emb F x).mpr h
      exact (card F i).ge
    · obtain ⟨i,rfl⟩ := (range_emb Y x).mpr h
      exact (by decide : 4≤12).trans_eq (card Y i).symm
  · exact RegionalFourSixEight.pair_card apart F Y
  · exact ⟨atPoint F 0,Or.inl (F 0).property,card F 0⟩
  · exact ⟨atPoint Y 0,Or.inr (Y 0).property,card Y 0⟩

theorem cycleAttach (F : Shore c₀ l I) (S : Shore c₀ r I) (Y : Shore c₀ v Twelve) (B : Layout F Y) (C : Around B)
    (lr : l≠r) (lv : l≠v) (rv : r≠v)
    (uniform : ∀ i j, c₀ (atPoint F i) (atPoint S j)=c₀ (atPoint F 0) (atPoint S 0))
    (reg : Nat → Prop) (cover : ∀ z, reg (c₀ z z) → c₀ z z=l ∨ c₀ z z=r ∨ c₀ z z=v) : Realizes p reg := by
  apply RegionalCycleExtension.attach_mapped p lr lv F Y (atPoint S 0) (S 0).property reg cover (pair p S Y rv)
    (fun i x hx => by obtain ⟨j,rfl⟩ := (range_emb S x).mpr hx; exact uniform i j) C.points C.label C.onto B.mark B.other B.different
  · intro j; rw [B.columns,C.pattern,Finset.map_map]
  · intro j i
    have hit : c₀ (atPoint Y j) (atPoint F (C.points i))=B.mark ↔ i∈edge (cycle (C.label j)) := by
      rw [B.cells,C.pattern]; exact Finset.mem_map' C.points.toEmbedding
    by_cases h : i∈edge (cycle (C.label j))
    · rw [if_pos h]; exact hit.mpr h
    · rw [if_neg h]; exact (B.palette j (C.points i)).resolve_left (mt hit.mp h)

theorem twinAttach (F : Shore c₀ l I) (S : Shore c₀ r I) (Y : Shore c₀ v Twelve)
    (rv : r≠v) (twin : FiberPairExtension.twins c₀ l v)
    (uniform : ∀ i j, c₀ (atPoint F i) (atPoint S j)=c₀ (atPoint F 0) (atPoint S 0))
    (reg : Nat → Prop) (cover : ∀ z, reg (c₀ z z) → c₀ z z=l ∨ c₀ z z=r ∨ c₀ z z=v) : Realizes p reg := by
  let keep := fun t => t=r ∨ t=v
  let y : Region c₀ keep := ⟨atPoint Y 0,(mem_vertices _ _ _).mpr (Or.inr (Y 0).property)⟩
  have t : FiberPairExtension.twins c₀ l (c₀ y.val y.val) := (Y 0).property.symm ▸ twin
  apply RegionalFourFourEight.restrict_map p (FiberPairExtension.attach p F 0 (by decide) keep (pair p S Y rv) y y ?_ t t)
    (fun x h => (cover x h).elim Or.inr Or.inl)
  intro j
  rcases (mem_vertices _ _ _).mp j.property with h|h
  · right; right
    intro i x z hz
    obtain ⟨a,ha⟩ := (range_emb F i.val).mpr i.property
    obtain ⟨b,hb⟩ := (range_emb F x.val).mpr x.property
    obtain ⟨c,hc⟩ := (range_emb S j.val).mpr h
    obtain ⟨d,hd⟩ := (range_emb S z).mpr (hz.trans h)
    simpa only [←show emb F a=atPoint F a from rfl,←show emb S c=atPoint S c from rfl,
      ←show emb F b=atPoint F b from rfl,←show emb S d=atPoint S d from rfl,ha,hb,hc,hd] using (uniform a c).trans (uniform b d).symm
  · exact Or.inl (h.trans (Y 0).property.symm)

end QGI.Coherent.LargeOrderTwelveCycle
