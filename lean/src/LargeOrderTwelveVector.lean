import LargeOrderTwelveTargets
import RegionalTernaryChoice

noncomputable section
namespace QGI.Coherent.LargeOrderTwelveVector
open SixTenCoordinates LargeOrderFourFourTwelveGeometry LargeOrderTwelveTargets LargeOrderSquareInterface
open FourTwelveCycle FourTwelveTypes SmallUnion SmallFiberExtension StrategyColorLaws Synchrony Intertwiner
open LargeFourteenRegion
open RegionalCycleExtension (emb range_emb)
open FourTwelveFunctional (source)
open Classical

variable {n k l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)
local notation "c₀" => source G
local notation "d₀" => targetName p

private theorem size_bound {m t : Nat} (f : Fin k → Fin n) (hf : Function.Injective f)
    (A : Finset (Fin k)) (Z : Shore c₀ t (Fin m)) (J : Finset (Fin m))
    (cover : ∀ i∈A, ∃ j∈J, atPoint Z j=f i) : A.card≤J.card := by
  let e : Fin k ↪ Fin n := ⟨f,hf⟩
  rw [←Finset.card_map e,←Finset.card_map (emb Z)]
  apply Finset.card_le_card
  intro z hz
  obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hz
  obtain ⟨j,hj,eq⟩ := cover i hi
  exact Finset.mem_map.mpr ⟨j,hj,eq⟩

attribute [local instance 2000] Classical.propDecidable

theorem based {reg : Nat → Prop} {f g : Fin k → Fin n} (D : DataFor p reg f g)
    (F : Shore c₀ l I) (S : Shore c₀ r I) (Y : Shore c₀ v Twelve) (B : Layout F Y)
    (strong : Nonempty (Around B) ∨ ∀ e, mult B.col e=2)
    (cover : ∀ z, reg (c₀ z z) → c₀ z z=l ∨ c₀ z z=r ∨ c₀ z z=v)
    (test : Fin k → Fin k → Prop) (a : Fin k)
    (match' : ∀ b, test b a → c₀ (f b) (f b)=c₀ (f a) (f a) ∧
      ∀ j, c₀ (f b) (atPoint F j)=c₀ (f a) (atPoint F j))
    (onS : ∀ j, atPoint S j=f a → ∃ J : Finset I, J.card≤3 ∧ ∀ b, test b a → ∀ t, atPoint S t=f b → t∈J) :
    (Finset.univ.filter (fun b => test b a)).card≤3 := by
  classical
  let A := Finset.univ.filter (fun b => test b a)
  rcases cover (f a) ((D.src _).mp ⟨a,rfl⟩) with h|h|h
  · obtain ⟨j,hj⟩ := (range_emb F _).mpr h
    apply (size_bound f D.injF A F {j} ?_).trans (by simp)
    intro b hb
    have eq := (match' b (Finset.mem_filter.mp hb).2).2 j
    rw [←hj] at eq
    exact ⟨j,by simp,(Relations.diagonal (closure G) eq).symm⟩
  · obtain ⟨j,hj⟩ := (range_emb S _).mpr h
    obtain ⟨J,bound,occ⟩ := onS j hj
    apply (size_bound f D.injF A S J ?_).trans bound
    intro b hb
    have hit := (Finset.mem_filter.mp hb).2
    obtain ⟨t,ht⟩ := (range_emb S _).mpr ((match' b hit).1.trans h)
    exact ⟨t,occ b hit t ht,ht⟩
  · obtain ⟨j,hj⟩ := (range_emb Y _).mpr h
    apply (size_bound f D.injF A Y (Finset.univ.filter (fun t => B.col t=B.col j)) ?_).trans (few B strong j)
    intro b hb
    have hit := (Finset.mem_filter.mp hb).2
    obtain ⟨t,ht⟩ := (range_emb Y _).mpr ((match' b hit).1.trans h)
    refine ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,edge_inj ?_⟩,ht⟩
    ext i
    rw [←B.cells,←B.cells]
    exact Iff.of_eq (congrArg (·=B.mark) (by simpa only [←ht,←hj] using (match' b hit).2 i))

theorem mixed (F : Shore c₀ l I) (S : Shore c₀ r I) (Y : Shore c₀ v Twelve)
    (lv : l≠v) (B : Layout F Y) (strong : Nonempty (Around B) ∨ ∀ e, mult B.col e=2)
    (nonuniform : ∃ i j, c₀ (atPoint F i) (atPoint S j)≠c₀ (atPoint F 0) (atPoint S 0))
    (reg : Nat → Prop) (active : ∀ i, reg (c₀ i i) → large G (c₀ i i))
    (cover : ∀ z, reg (c₀ z z) → c₀ z z=l ∨ c₀ z z=r ∨ c₀ z z=v) : Realizes p reg := by
  classical
  obtain ⟨M⟩ := model p F Y lv
  obtain ⟨ξ,e,nz,fix⟩ := fixed p B M strong
  apply LargeOrderBlocks.of_solver p reg active rfl
  intro f g D
  apply RegionalTernaryChoice.source_pins p D ξ nz (atPoint F) (fun i => atPoint M.four (e i)) fix
  intro a
  apply based p D F S Y B strong cover _ a (fun _ h => h)
  intro j hj
  obtain ⟨u,w,only⟩ := FourEightMixed.small_patterns (sourceLaws (closure G)) F S nonuniform j
  refine ⟨{u,w},by have h := Finset.card_insert_le u ({w} : Finset I); simpa using h.trans (by simp : ({w} : Finset I).card+1≤3),?_⟩
  intro b hit t ht
  simp only [Finset.mem_insert,Finset.mem_singleton]
  exact only t (fun i => Relations.transpose _ (by simpa only [←ht,←hj] using hit.2 i))

end QGI.Coherent.LargeOrderTwelveVector
