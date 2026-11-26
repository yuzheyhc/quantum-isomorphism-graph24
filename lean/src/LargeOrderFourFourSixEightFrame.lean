import LargeOrderSixHalves
import LargeOrderSingleCycle
import TwoShoreAttachment
import RegionalFourFourEight
import RegionalFourSixEight

noncomputable section
namespace QGI.Coherent.LargeOrderFourFourSixEightFrame
open SmallUnion SmallFiberExtension LargeFourteenRegion StrategyColorLaws SixTenCoordinates SixEightGeometry
open FourTwelveFunctional (source fiber_eq)
open FourEightGeometry (Eight)
open SixEightCatalog (Six)
open SixSixEightPins (Flat)
open RegionalCycleExtension (emb range_emb)
open private twins reverse from RegionalFourFourEight

structure Quad {n : Nat} (G : Graph n) where
  a : Nat
  b : Nat
  s : Nat
  v : Nat
  A : Shore (source G) a (Fin 4)
  B : Shore (source G) b (Fin 4)
  S : Shore (source G) s Six
  Y : Shore (source G) v Eight
  ab : a≠b

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (p : PerfectStrategy G H K) (Q : Quad G)
local notation "c₀" => source G

abbrev Quad.whole (Q : Quad G) (t : Nat) := t=Q.a ∨ t=Q.b ∨ t=Q.s ∨ t=Q.v
abbrev Quad.withoutA (Q : Quad G) (t : Nat) := t=Q.b ∨ t=Q.s ∨ t=Q.v
abbrev Quad.withoutS (Q : Quad G) (t : Nat) := t=Q.a ∨ t=Q.b ∨ t=Q.v
def Quad.swap (Q : Quad G) : Quad G := ⟨Q.b,Q.a,Q.s,Q.v,Q.B,Q.A,Q.S,Q.Y,Ne.symm Q.ab⟩

theorem swapped (map : Realizes p Q.swap.whole) : Realizes p Q.whole :=
  RegionalFourFourEight.restrict_map p map (fun i h => by change _=_ ∨ _=_ ∨ _=_ ∨ _=_ at h ⊢; tauto)

theorem size {l m : Nat} (A : Shore c₀ l (Fin m)) {x : Fin n} (hx : c₀ x x=l) : (fiber G x).card=m := by
  have eq : fiber G x=vertices c₀ (·=l) := by ext i; rw [fiber_eq,mem_vertices]; change (c₀ i i=c₀ x x ↔ c₀ i i=l); rw [hx]
  rw [eq,RegionalTwoAnchor.card A]

theorem apart {l r k m : Nat} (F : Shore c₀ l (Fin k)) (Y : Shore c₀ r (Fin m)) (ne : k≠m) : l≠r := by
  intro eq
  apply ne
  exact (RegionalTwoAnchor.card F).symm.trans ((congrArg (fun s => (vertices c₀ (·=s)).card) eq).trans (RegionalTwoAnchor.card Y))

theorem active (i : Fin n) (h : Q.whole (c₀ i i)) : large G (c₀ i i) := by
  change 3 < (vertices c₀ (·=c₀ i i)).card
  rcases h with ha|hb|hs|hy
  · rw [ha,RegionalTwoAnchor.card Q.A]; decide
  · rw [hb,RegionalTwoAnchor.card Q.B]; decide
  · rw [hs,RegionalTwoAnchor.card Q.S]; decide
  · rw [hy,RegionalTwoAnchor.card Q.Y]; decide

theorem oldA : Realizes p Q.withoutA :=
  RegionalFourSixEight.solve p (apart Q.B Q.S (by decide)) (apart Q.B Q.Y (by decide)) (apart Q.S Q.Y (by decide))
    Q.B Q.S Q.Y Q.withoutA (fun i h => active Q i (Or.inr h)) (fun _ h => h)

theorem oldS : Realizes p Q.withoutS := by
  apply RegionalFourFourEight.solve p Q.ab (apart Q.A Q.Y (by decide)) (apart Q.B Q.Y (by decide))
    Q.A Q.B Q.Y Q.withoutS _ (fun _ h => h)
  intro i h
  apply active Q i
  rcases h with h|h|h <;> tauto

theorem oldSY : Realizes p (fun t => t=Q.s ∨ t=Q.v) := by
  apply LargeOrderBlocks.fourteen p _ _ (RegionalFourSixEight.pair_card (apart Q.S Q.Y (by decide)) Q.S Q.Y)
  intro i h; exact active Q i (Or.inr (Or.inr h))

theorem thin {l : Nat} (inside : Q.withoutA l) (one : LargeOrderSquareInterface.MapsOne c₀ l Q.a) : Realizes p Q.whole := by
  obtain ⟨x,y,hx,hy,h⟩ := one
  exact RegionalFourFourEight.functional p (oldA p Q) (fun _ q => Or.symm q) x y (hx.symm ▸ inside) hy h

theorem alone (ba : Flat Q.A Q.B) (sa : Flat Q.A Q.S) : Realizes p Q.whole := by
  apply LargeOrderSingleCycle.attach p Q.A Q.Y Q.withoutA Q.whole (Or.inr (Or.inr rfl)) (oldA p Q) (fun _ h => h)
  intro i j u w hi hj nv hu hw
  rcases hj with hb|hs|hv
  · exact LargeOrderSingleCycle.flat_at Q.A Q.B ba hi hb hu (hw.trans hb)
  · exact LargeOrderSingleCycle.flat_at Q.A Q.S sa hi hs hu (hw.trans hs)
  · exact (nv hv).elim

theorem weakA (ab : FiberPairExtension.twins c₀ Q.a Q.b) (as' : Flat Q.A Q.S) (ay : Flat Q.A Q.Y) : Realizes p Q.whole := by
  apply LargeOrderSingleCycle.weak p Q.A Q.B (by decide) 0 Q.withoutA Q.whole (Or.inl rfl) (oldA p Q) (fun _ h => h) _ ab
  intro i j u w ha hj ne hu hw
  rcases hj with hb|hs|hy
  · exact (ne hb).elim
  · exact LargeOrderSingleCycle.flat_at Q.A Q.S as' ha hs hu (hw.trans hs)
  · exact LargeOrderSingleCycle.flat_at Q.A Q.Y ay ha hy hu (hw.trans hy)

theorem group (as' : Flat Q.A Q.S) (bs : Flat Q.B Q.S) (ay : FiberPairExtension.twins c₀ Q.a Q.v)
    (by' : FiberPairExtension.twins c₀ Q.b Q.v) : Realizes p Q.whole := by
  let keep := fun t => t=Q.s ∨ t=Q.v
  let y : Region c₀ keep := ⟨atPoint Q.Y 0,(mem_vertices _ _ _).mpr (Or.inr (Q.Y 0).property)⟩
  apply RegionalFourFourEight.restrict_map p (TwoShoreAttachment.attach p (atPoint Q.A 0) (atPoint Q.B 0)
    (Q.A 0).property (Q.B 0).property ((RegionalTwoAnchor.pair_bound Q.A Q.B).trans (by decide))
    keep (oldSY p Q) y (Q.Y 0).property ay by' ?_)
  · intro i h; rcases h with ha|hb|hs|hy <;> tauto
  · intro i j u w h hx ne hu hw
    have hs := hx.resolve_right ne
    rcases h with ha|hb
    · exact LargeOrderSingleCycle.flat_at Q.A Q.S as' ha hs (hu.trans ha) (hw.trans hs)
    · exact LargeOrderSingleCycle.flat_at Q.B Q.S bs hb hs (hu.trans hb) (hw.trans hs)

theorem removeS {m l : Nat} [NeZero (2*m)] (sm : m=2 ∨ m=4) (F : Shore c₀ l (Fin (2*m)))
    (inside : Q.withoutS l) (weak : FiberPairExtension.twins c₀ l Q.s) (mixed : ¬Flat F Q.S) : Realizes p Q.whole := by
  classical
  have ne : ∃ i j, c₀ (atPoint F i) (atPoint Q.S j)≠c₀ (atPoint F 0) (atPoint Q.S 0) := by
    simpa only [Flat,rect,not_forall] using mixed
  apply RegionalFourFourEight.restrict_map p (LargeOrderSixHalves.extend p sm Q.S F weak ne Q.withoutS (oldS p Q) inside ?_)
  · intro i h; rcases h with ha|hb|hs|hy <;> tauto
  · intro x
    rcases (mem_vertices _ _ _).mp x.property with h|h|h
    · exact Or.inl (size Q.A h)
    · exact Or.inl (size Q.B h)
    · exact Or.inr (size Q.Y h)

theorem add_card {l m : Nat} (F : Shore c₀ l (Fin m)) (rest : Nat → Prop) (away : ¬rest l) :
    (vertices c₀ (fun t => t=l ∨ rest t)).card=m+(vertices c₀ rest).card := by
  have eq : vertices c₀ (fun t => t=l ∨ rest t)=vertices c₀ (·=l) ∪ vertices c₀ rest := by
    ext i; simp only [mem_vertices,Finset.mem_union]
  have dis : Disjoint (vertices c₀ (·=l)) (vertices c₀ rest) := by
    apply Finset.disjoint_left.mpr; intro i hi hr; exact away (((mem_vertices _ _ _).mp hi) ▸ (mem_vertices _ _ _).mp hr)
  rw [eq,Finset.card_union_of_disjoint dis,RegionalTwoAnchor.card F]

theorem card : (vertices c₀ Q.whole).card=22 := by
  change (vertices c₀ (fun t => t=Q.a ∨ Q.withoutA t)).card=22
  rw [add_card Q.A Q.withoutA (fun h => h.elim Q.ab (fun h => h.elim (apart Q.A Q.S (by decide)) (apart Q.A Q.Y (by decide))))]
  change 4+(vertices c₀ (fun t => t=Q.b ∨ t=Q.s ∨ t=Q.v)).card=22
  rw [add_card Q.B (fun t => t=Q.s ∨ t=Q.v) (fun h => h.elim (apart Q.B Q.S (by decide)) (apart Q.B Q.Y (by decide))),
    RegionalFourSixEight.pair_card (apart Q.S Q.Y (by decide)) Q.S Q.Y]

theorem isolateY (ay : Flat Q.A Q.Y) (by' : Flat Q.B Q.Y) (sy : Flat Q.S Q.Y) : Realizes p Q.whole := by
  let keep := fun t => t=Q.a ∨ t=Q.b ∨ t=Q.s
  have old : Realizes p keep := by
    apply LargeOrderBlocks.fourteen p keep _ _
    · intro i h; apply active Q i; rcases h with h|h|h <;> tauto
    · change (vertices c₀ (fun t => t=Q.a ∨ t=Q.b ∨ t=Q.s)).card=14
      rw [add_card Q.A (fun t => t=Q.b ∨ t=Q.s) (fun h => h.elim Q.ab (apart Q.A Q.S (by decide))),
        RegionalFourSixEight.pair_card (apart Q.B Q.S (by decide)) Q.B Q.S]
  apply LargeOrderSingleCycle.weak p Q.Y Q.A (by decide) 0 keep Q.whole (Or.inl rfl) old _ _
    (twins Q.Y Q.A (SixSixEightPins.flat_twins _ _ (SixSixEightPins.flip_flat _ _ ay)))
  · intro i h; rcases h with h|h|h|h <;> tauto
  · intro i j u w hi hj ne hu hw
    rcases hj with ha|hb|hs
    · exact (ne ha).elim
    · exact LargeOrderSingleCycle.flat_at Q.Y Q.B (SixSixEightPins.flip_flat _ _ by') hi hb hu (hw.trans hb)
    · exact LargeOrderSingleCycle.flat_at Q.Y Q.S (SixSixEightPins.flip_flat _ _ sy) hi hs hu (hw.trans hs)

end QGI.Coherent.LargeOrderFourFourSixEightFrame
