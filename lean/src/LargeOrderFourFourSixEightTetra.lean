import LargeOrderFourFourSixEightFrame
import LargeOrderFourSixRank
import LargeOrderFourShorePins

noncomputable section
namespace QGI.Coherent.LargeOrderFourFourSixEightTetra
open SixTenCoordinates SixEightGeometry SmallUnion SmallFiberExtension Intertwiner Synchrony RegionalPins
open LargeOrderFourFourSixEightFrame LargeOrderFourShorePins
open SixSixEightPins (Flat flip_flat)
open RegionalCycleExtension (emb range_emb)
open FourTwelveFunctional (source)
open private twins reverse from RegionalFourFourEight

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (p : PerfectStrategy G H K) (Q : Quad G)
local notation "c₀" => source G

theorem solve (t : Nat) (map : Equiv.Perm (Fin 6)) (inc : ∀ i j, rect Q.A Q.S i j=t ↔ FourSixSix.incident i (map j)) :
    Realizes p Q.whole := by
  classical
  let law := sourceLaws (closure G)
  by_cases bs : Flat Q.B Q.S
  · have ab := LargeOrderFourSixRank.uniform law Q.A Q.S Q.B t map inc (flip_flat _ _ bs)
    exact swapped p Q (alone p Q.swap (flip_flat _ _ ab) bs)
  by_cases sy : Flat Q.S Q.Y
  · have ay := LargeOrderFourSixRank.uniform law Q.A Q.S Q.Y t map inc sy
    rcases FourSixSix.Interfaces.classify law Q.B Q.S with ⟨v,all⟩|weak|⟨v,m,h⟩
    · exact (bs (fun i j => (all i j).trans (all 0 0).symm)).elim
    · exact removeS p Q (m:=2) (Or.inl rfl) Q.B (Or.inr (Or.inl rfl)) weak bs
    · exact isolateY p Q ay (LargeOrderFourSixRank.uniform law Q.B Q.S Q.Y v m h sy) sy
  rcases OddHalfPartition.short_or_twins law Q.S Q.Y with weak|short
  · exact removeS p Q (m:=4) (Or.inr rfl) Q.Y (Or.inr (Or.inr rfl)) (reverse (twins Q.S Q.Y weak))
      (fun h => sy (flip_flat _ _ h))
  obtain ⟨ξ,nz,pa,ps⟩ := RegionalFourSixEightTetra.pins p Q.A Q.S t map inc
  apply reverse_pins p Q.whole (active Q) ξ nz
  intro x h
  rcases h with ha|hb|hs|hy
  · obtain ⟨i,rfl⟩ := (range_emb Q.A _).mpr ha
    exact named (pa i)
  · apply small Q.B hb
    intro i
    let U := Finset.univ.filter (fun b => ∀ j, rect Q.B Q.S b j=rect Q.B Q.S i j)
    obtain ⟨a,b,whereAt⟩ := DegreeClassRigidity.two_labels U 0 (ShoreSignatureSize.half law Q.B Q.S bs i)
    exact ⟨a,b,fun k eq => whereAt k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun j => (eq _ (ps j)).symm⟩)⟩
  · obtain ⟨i,rfl⟩ := (range_emb Q.S _).mpr hs
    exact named (ps i)
  · apply small Q.Y hy
    intro i
    obtain ⟨a,b,occ⟩ := short i
    exact ⟨a,b,fun j h => occ j (fun z => Relations.transpose _ (h _ (ps z)))⟩

end QGI.Coherent.LargeOrderFourFourSixEightTetra
