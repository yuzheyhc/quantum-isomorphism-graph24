import LargeOrderEightCycles
import FiberPairExtension
import SixSixEightPins

noncomputable section
namespace QGI.Coherent.LargeOrderSingleCycle
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws FourEightGeometry
open RegionalCycleExtension (emb range_emb)
open FourTwelveFunctional (source)
open SixSixEightPins (Flat)
open private twins from RegionalFourFourEight
variable {n l v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)
local notation "c₀" => source G

theorem flat_at {k m l r : Nat} [NeZero k] [NeZero m] (F : Shore c₀ l (Fin k)) (Y : Shore c₀ r (Fin m))
    (h : Flat F Y) {i j u w : Fin n} (hi : c₀ i i=l) (hj : c₀ j j=r) (hu : c₀ u u=l) (hw : c₀ w w=r) :
    c₀ i j=c₀ u w := by
  obtain ⟨i,rfl⟩ := (range_emb F i).mpr hi; obtain ⟨j,rfl⟩ := (range_emb Y j).mpr hj
  obtain ⟨u,rfl⟩ := (range_emb F u).mpr hu; obtain ⟨w,rfl⟩ := (range_emb Y w).mpr hw
  exact (h i j).trans (h u w).symm

theorem weak {m q : Nat} [NeZero m] (F : Shore c₀ l (Fin q)) (Y : Shore c₀ v (Fin m))
    (small : q≤13) (base : Fin q) (keep reg : Nat → Prop) (inside : keep v) (old : Realizes p keep)
    (cover : ∀ i, reg (c₀ i i) → c₀ i i=l ∨ keep (c₀ i i))
    (flat : ∀ i j u w : Fin n, c₀ i i=l → keep (c₀ j j) → c₀ j j≠v → c₀ u u=l → c₀ w w=c₀ j j → c₀ i j=c₀ u w)
    (h : FiberPairExtension.twins c₀ l v) : Realizes p reg := by
  let anchor : Region c₀ keep := ⟨atPoint Y 0,(mem_vertices _ _ _).mpr ((Y 0).property.symm ▸ inside)⟩
  have tag : c₀ anchor.val anchor.val=v := (Y 0).property
  apply RegionalFourFourEight.restrict_map p (FiberPairExtension.attach p F base small keep old anchor anchor ?_ (tag.symm ▸ h) (tag.symm ▸ h))
  · exact fun i h => Or.symm (cover i h)
  · intro j
    by_cases eq : c₀ j.val j.val=v
    · exact Or.inl (eq.trans tag.symm)
    · exact Or.inr (Or.inr (fun i u w hw => flat _ j.val _ w i.property ((mem_vertices _ _ _).mp j.property) eq u.property hw))

/-- Adjoin a four-point fiber with one possibly nonuniform external
eight-point fiber. The old map can live on an arbitrarily large region. -/
theorem attach (F : Shore c₀ l (Fin 4)) (Y : Shore c₀ v Eight)
    (keep reg : Nat → Prop) (inside : keep v) (old : Realizes p keep)
    (cover : ∀ i, reg (c₀ i i) → c₀ i i=l ∨ keep (c₀ i i))
    (flat : ∀ i j u w : Fin n, c₀ i i=l → keep (c₀ j j) → c₀ j j≠v → c₀ u u=l → c₀ w w=c₀ j j → c₀ i j=c₀ u w) :
    Realizes p reg := by
  rcases FourEightGeometry.interface F Y with ⟨i,j,one⟩|sync|⟨t,w,pal,b,cells,⟨C⟩⟩
  · exact RegionalFourFourEight.functional p old (fun x h => Or.symm (cover x h)) (atPoint Y j) (atPoint F i)
      ((Y j).property.symm ▸ inside) (F i).property one
  · exact weak p F Y (by decide) 0 keep reg inside old cover flat (twins F Y sync)
  · obtain ⟨a,z,az,rows,names⟩ := RegionalCycleExtension.edges F Y t w pal b cells C
    have full (k) : ∃ i, C.label i=k := by
      obtain ⟨j,mem⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter (fun i => C.label i=k)).card by rw [C.twice]; decide)
      exact ⟨j,(Finset.mem_filter.mp mem).2⟩
    exact RegionalCycleExtension.attach_to p F Y keep reg inside cover old flat C.points C.label full a z az rows names

end QGI.Coherent.LargeOrderSingleCycle
