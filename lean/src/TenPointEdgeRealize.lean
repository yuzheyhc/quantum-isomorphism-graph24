import TenPointCrossEdges
import RegionalTenTenSmall

noncomputable section
namespace QGI.Coherent.TenPointEdgeRealize
open TenPointCross TenPointCrossLaws
open SixTenCoordinates (Shore atPoint sourceLaws Block)
open SmallUnion SmallFiberExtension
open FourTwelveFunctional (source)

variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (F : Shore (source G) l V) (Y : Shore (source G) r V)

attribute [local irreducible] matrices Edges.candidates
set_option maxHeartbeats 1500000 in
theorem simple {a : Key} (chart : Chart F a) (v : Nat) (sz : ∀ i, (row F Y v i).card=2)
    (min : ∀ i j, 2≤(col F Y (entry F Y i j) j).card) (inj : Function.Injective (col F Y v))
    (reg : Nat → Prop) (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) : Realizes p reg := by
  classical
  let C := col F Y v
  have ok (j) := (constraints F Y (sourceLaws _) chart v 2 j sz min).1
  obtain ⟨j,hj⟩ := Finset.card_pos.mp ((by decide : 0<2).trans_eq (sz 0).symm)
  have flag0 : entry F Y 0 j=v := (Finset.mem_filter.mp hj).2
  have zero : (0:V)∈C j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,flag0⟩
  let bank := Edges.bank a (C j)
  have inside (k) : C k∈bank := by
    have positive : 0<(C k).card := (by decide : 0<2).trans_eq (ok k).1.symm
    obtain ⟨i,hi⟩ := Finset.card_pos.mp positive
    have hit : entry F Y i k=v := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Edges.occurs (ok k),i,hi,funext (fun z => count_block F Y (sourceLaws _) chart v (hit.trans flag0.symm) _)⟩
  have all : 10≤bank.card := by
    have inc : (Finset.univ.image C)⊆bank := by rintro s hs; obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hs; exact inside k
    have eq := Finset.card_image_of_injective (Finset.univ : Finset V) inj
    exact (show 10=(Finset.univ.image C).card from (Fintype.card_fin 10).symm.trans ((Finset.card_univ).symm.trans eq.symm)).le.trans (Finset.card_le_card inc)
  have short := Edges.short_of_full (ok j) zero all
  let root := atPoint F (0:V)
  have left := RegionalShorePins.one F root (fun i => (Finset.card_le_card (t:=Finset.univ.filter (fun k : V => cell a k 0=cell a i 0)) (by
    intro k h; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(chart _ _ _ _).mp (Finset.mem_filter.mp h).2⟩)).trans (short.1 i))
  have right := RegionalShorePins.one Y root (fun k => (RegionalSignatureBound.bound_set C inj id _
    (bank.filter (fun s => sig a s 0=sig a (C k) 0)) (by
      intro t ht
      have eq : entry F Y 0 t=entry F Y 0 k := Relations.transpose _ (Finset.mem_filter.mp ht).2
      exact ⟨C t,Finset.mem_filter.mpr ⟨inside t,funext (fun z => count_block F Y (sourceLaws _) chart v eq _)⟩,rfl⟩)).trans (short.2 _ (inside k)))
  apply RegionalShorePins.root p F Y Y reg _ (fun i h => (cover i h).imp_right Or.inl) root left right right
  intro i h; rcases cover i h with h|h
  · rw [h,LargeFourteenRegion.large,RegionalTwoAnchor.card F]; decide
  · rw [h,LargeFourteenRegion.large,RegionalTwoAnchor.card Y]; decide

end QGI.Coherent.TenPointEdgeRealize
