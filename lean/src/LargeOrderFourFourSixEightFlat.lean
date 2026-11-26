import LargeOrderFourFourSixEightFrame
import LargeOrderFourShorePins
import LargeOrderSixEightCuts

noncomputable section
namespace QGI.Coherent.LargeOrderFourFourSixEightFlat
open SmallUnion SmallFiberExtension StrategyColorLaws SixTenCoordinates SixEightGeometry
open LargeOrderFourFourSixEightFrame LargeOrderEightCycles LargeOrderSquareInterface
open SixSixEightPins (Flat flip_flat flat_twins)
open FourTwelveFunctional (source)
open private twins reverse from RegionalFourFourEight

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (p : PerfectStrategy G H K) (Q : Quad G)
local notation "c₀" => source G

private theorem narrow {l v m : Nat} [NeZero m] (F : Shore c₀ l (Fin 4)) (Y : Shore c₀ v (Fin m))
    (mix : ¬Flat F Y) (j : Fin m) (i : Fin 4) : (Finset.univ.filter (fun b => rect F Y b j=rect F Y i j)).card≤3 := by
  classical
  let t := rect F Y i j
  let B := fun z s => decide (rect F Y z s=t)
  have named : Block F F Y Y B B := fun ⦃_ _ _ _⦄ h => congrArg (fun v => decide (v=t)) h
  have same (s) := Block.degree_eq (sourceLaws _) (Block.flip (sourceLaws _) named) s j
  by_contra! big
  have card (s) : (Finset.univ.filter (fun b => rect F Y b s=t)).card=4 := by
    have le := Finset.card_le_univ (Finset.univ.filter (fun b => rect F Y b j=t))
    have eq : (Finset.univ.filter (fun b => rect F Y b j=t)).card=4 := by
      change _≤4 at le
      change 3<(Finset.univ.filter (fun b => rect F Y b j=t)).card at big
      exact Nat.le_antisymm le (by omega)
    simpa only [B,FiberRectangles.degree,decide_eq_true_eq,eq] using same s
  have full (i s) : rect F Y i s=t := by
    have all := Finset.eq_univ_of_card (Finset.univ.filter (fun b => rect F Y b s=t)) (card s)
    have mem : i∈Finset.univ.filter (fun b => rect F Y b s=t) := by rw [all]; exact Finset.mem_univ i
    exact (Finset.mem_filter.mp mem).2
  exact mix (fun i j => (full i j).trans (full 0 0).symm)

private theorem y_thin (i : Fin 4) (j : Fin 8)
    (one : ∀ z, c₀ (atPoint Q.Y j) z=c₀ (atPoint Q.Y j) (atPoint Q.A i) → z=atPoint Q.A i) : Realizes p Q.whole :=
  thin p Q (Or.inr (Or.inr rfl)) ⟨atPoint Q.Y j,atPoint Q.A i,(Q.Y j).property,(Q.A i).property,one⟩

private theorem flat_side (as' : Flat Q.A Q.S) (bs : Flat Q.B Q.S) (ay : Flat Q.A Q.Y) : Realizes p Q.whole := by
  rcases FourEightGeometry.interface Q.B Q.Y with ⟨i,j,one⟩|by'|⟨t,w,pal,b,mark,⟨C⟩⟩
  · exact swapped p Q (y_thin p Q.swap i j one)
  · exact group p Q as' bs (twins Q.A Q.Y (flat_twins _ _ ay)) (twins Q.B Q.Y by')
  · let D : CycleData Q.B Q.Y := ⟨t,w,pal,b,mark,C⟩
    rcases square (sourceLaws _) Q.B Q.A with one|weak|cy
    · exact thin p Q (Or.inl rfl) one
    · exact weakA p Q (reverse weak) as' ay
    · exact thin p Q (Or.inr (Or.inr rfl)) (conflict D (cycle_reverse (sourceLaws _) cy))

theorem solve (as' : Flat Q.A Q.S) (bs : Flat Q.B Q.S) : Realizes p Q.whole := by
  classical
  by_cases weak : SplitRectangle.Twins (rect Q.S Q.Y)
  · apply LargeOrderSingleCycle.weak p Q.S Q.Y (by decide) 0 Q.withoutS Q.whole (Or.inr (Or.inr rfl)) (oldS p Q) _
      _ (twins Q.S Q.Y weak)
    · intro i h; rcases h with h|h|h|h <;> tauto
    · intro i j u w hi hj nv hu hw
      rcases hj with ha|hb|hy
      · exact LargeOrderSingleCycle.flat_at Q.S Q.A (flip_flat _ _ as') hi ha hu (hw.trans ha)
      · exact LargeOrderSingleCycle.flat_at Q.S Q.B (flip_flat _ _ bs) hi hb hu (hw.trans hb)
      · exact (nv hy).elim
  rcases LargeOrderSixEightCuts.cut Q.S Q.Y (apart Q.S Q.Y (by decide)) weak with cube|forbidden
  · by_cases ay : Flat Q.A Q.Y
    · exact flat_side p Q as' bs ay
    by_cases by' : Flat Q.B Q.Y
    · exact swapped p Q (flat_side p Q.swap bs as' by')
    have sy := (SixEightGeometry.classify (apart Q.S Q.Y (by decide)) Q.S Q.Y).1.resolve_left (fun h => weak (flat_twins _ _ h))
    apply LargeOrderFourShorePins.root p Q.whole (active Q) (atPoint Q.Y 0)
    intro b h
    rcases h with ha|hb|hs|hy
    · exact ⟨_,_,Q.A,ha,narrow Q.A Q.Y ay 0⟩
    · exact ⟨_,_,Q.B,hb,narrow Q.B Q.Y by' 0⟩
    · exact ⟨_,_,Q.S,hs,sy 0⟩
    · refine ⟨_,_,Q.Y,hy,fun i => ?_⟩
      apply (Finset.card_le_card ?_).trans (cube 0 i)
      intro b ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Relations.transpose _ (Finset.mem_filter.mp ht).2⟩
  · rcases FourEightGeometry.interface Q.A Q.Y with ⟨i,j,one⟩|aw|⟨v,w,pal,b,cells,⟨C⟩⟩
    · exact y_thin p Q i j one
    · rcases FourEightGeometry.interface Q.B Q.Y with ⟨i,j,one⟩|bw|⟨v,w,pal,b,cells,⟨C⟩⟩
      · exact swapped p Q (y_thin p Q.swap i j one)
      · exact group p Q as' bs (twins Q.A Q.Y aw) (twins Q.B Q.Y bw)
      · exact (forbidden Q.B (flip_flat _ _ bs) ⟨⟨v,w,pal,b,cells,C⟩⟩).elim
    · exact (forbidden Q.A (flip_flat _ _ as') ⟨⟨v,w,pal,b,cells,C⟩⟩).elim

end QGI.Coherent.LargeOrderFourFourSixEightFlat
