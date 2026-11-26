import LargeOrderFourFourTwelve
import FourSixSixSixRoot
import RegionalSixTwelveComplete

noncomputable section
namespace QGI.Coherent.FourSixTwelveCases
open SixTenCoordinates LargeOrderSquareInterface LargeOrderFourFourTwelveGeometry LargeOrderTwelveTargets
open SmallUnion SmallFiberExtension StrategyColorLaws LargeFourteenRegion FourTwelveCycle RegionalShorePins
open FourTwelveTypes
open RegionalCycleExtension (emb range_emb)
open FourTwelveFunctional (source)
open private twins from RegionalFourFourEight
open private six from FourSixSixSixRoot
variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)
local notation "c₀" => source G

private theorem cycleAttach (F : Shore c₀ l I) (S : Shore c₀ r (Fin 6)) (Y : Shore c₀ v Twelve) (B : Layout F Y) (C : Around B)
    (lr : l≠r) (lv : l≠v) (rv : r≠v)
    (uniform : ∀ i j, c₀ (atPoint F i) (atPoint S j)=c₀ (atPoint F 0) (atPoint S 0))
    (reg : Nat → Prop) (cover : ∀ z, reg (c₀ z z) → c₀ z z=l ∨ c₀ z z=r ∨ c₀ z z=v) : Realizes p reg := by
  apply RegionalCycleExtension.attach_mapped p lr lv F Y (atPoint S 0) (S 0).property reg cover (RegionalSixTwelve.solve p S Y _ (fun _ h => h))
    (fun i x hx => by obtain ⟨j,rfl⟩ := (range_emb S x).mpr hx; exact uniform i j) C.points C.label C.onto B.mark B.other B.different
  · intro j; rw [B.columns,C.pattern,Finset.map_map]
  · intro j i
    have hit : c₀ (atPoint Y j) (atPoint F (C.points i))=B.mark ↔ i∈edge (cycle (C.label j)) := by
      rw [B.cells,C.pattern]; exact Finset.mem_map' C.points.toEmbedding
    by_cases h : i∈edge (cycle (C.label j))
    · rw [if_pos h]; exact hit.mpr h
    · rw [if_neg h]; exact (B.palette j (C.points i)).resolve_left (mt hit.mp h)

private theorem shortY (F : Shore c₀ l I) (Y : Shore c₀ v Twelve) (B : Layout F Y)
    (h : Nonempty (Around B) ∨ ∀ e, mult B.col e=2) : Short Y (atPoint F) := by
  intro j
  apply (Finset.card_le_card ?_).trans (few B h j)
  intro k hk
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hk
  apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _,edge_inj ?_⟩
  ext i
  rw [←B.cells,←B.cells,hk]

theorem reduce (F : Shore c₀ l I) (S : Shore c₀ r (Fin 6)) (Y : Shore c₀ v Twelve)
    (lr : l≠r) (lv : l≠v) (rv : r≠v) (reg : Nat → Prop) (active : ∀ i, reg (c₀ i i) → large G (c₀ i i))
    (cover : ∀ z, reg (c₀ z z) → c₀ z z=l ∨ c₀ z z=r ∨ c₀ z z=v)
    (root : ∀ (t : Nat) (m : Equiv.Perm (Fin 6)),
      (∀ i j, c₀ (atPoint F i) (atPoint S j)=t ↔ FourSixSix.incident i (m j)) → Realizes p reg)
    (repeated : ∀ B : Layout F Y, (∀ e, mult B.col e=2) → SixSixEightPins.Flat F S → Realizes p reg) :
    Realizes p reg := by
  classical
  have old := RegionalSixTwelve.solve p S Y (fun w => w=r ∨ w=v) (fun _ h => h)
  rcases classify F Y lv with thin|fy|⟨B,strong⟩
  · obtain ⟨x,y,dx,dy,one⟩ := thin
    exact RegionalFourFourEight.functional p old (fun z h => (cover z h).symm) x y (Or.inr dx) dy one
  · apply Or.elim (FourSixSix.Interfaces.classify (sourceLaws _) F S)
    · rintro ⟨t,all⟩
      apply RegionalFourFourEight.centered p F S Y (by decide) old cover (twins F S ?_) fy
      exact ⟨fun i x _ _ j => (all i j).trans (all x j).symm,fun _ j z _ i => (all i j).trans (all i z).symm⟩
    · rintro (ts|⟨t,m,inc⟩)
      · exact RegionalFourFourEight.centered p F S Y (by decide) old cover ts fy
      · exact root t m inc
  · by_cases flat : SixSixEightPins.Flat F S
    · rcases strong with cy|twice
      · exact cycleAttach p F S Y B (Classical.choice cy) lr lv rv flat reg cover
      · exact repeated B twice flat
    obtain ⟨M⟩ := model p F Y lv
    obtain ⟨ξ,e,nz,fix⟩ := fixed p B M strong
    exact RegionalShorePins.realize p F S Y reg active cover ξ nz (atPoint F) _ fix (pinned F)
      (RegionalMarkPins.widen S (six F S flat) (fun _ => ⟨0,rfl⟩)) (shortY F Y B strong)
end QGI.Coherent.FourSixTwelveCases
