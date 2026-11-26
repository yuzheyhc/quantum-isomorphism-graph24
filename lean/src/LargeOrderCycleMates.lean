import LargeOrderEightCycles
import OddHalfPartition

noncomputable section
namespace QGI.Coherent.LargeOrderCycleMates
open LargeOrderEightCycles SixTenCoordinates FourTwelveCycle
open FourEightGeometry (Eight)
open FourTwelveFunctional (source)
open RegionalCycleExtension (emb)

theorem mate {n l r} {G : Graph n} {F : Shore (source G) l (Fin 4)} {Y : Shore (source G) r Eight}
    (D : CycleData F Y) (j : Eight) :
    ∃ k, k≠j ∧ (∀ z, source G (atPoint Y j) (atPoint Y z)=source G (atPoint Y j) (atPoint Y k) → z=k) ∧
      ∀ i, source G (atPoint F i) (atPoint Y j)=source G (atPoint F i) (atPoint Y k) := by
  classical
  let B := fun z i => decide (i∈edge (D.code z))
  have cells (z i) : B z i=true ↔ source G (atPoint F i) (atPoint Y z)=D.mark := by
    simp only [B,decide_eq_true_eq]; exact (D.cells i z).symm
  have deg (z) : FiberRectangles.degree (B z)=2 := by
    change (Finset.univ.filter (fun i => decide (i∈edge (D.code z))=true)).card=2
    simpa only [decide_eq_true_eq,Finset.filter_mem_eq_inter,Finset.univ_inter] using
      (show (edge (D.code z)).card=2 from (by native_decide : ∀ e : Edge, (edge e).card=2) _)
  have named := OddHalfPartition.column_block (SixTenCoordinates.sourceLaws _) F Y B cells deg
  have eq (z h) : B z=B h ↔ D.cycle.label z=D.cycle.label h := by
    have line : Function.Injective (fun i : Fin 4 => edge (cycle i)) := by native_decide
    constructor
    · intro same
      have identical : edge (D.code z)=edge (D.code h) := by
        ext i; exact decide_eq_decide.mp (congrFun same i)
      rw [D.cycle.edges,D.cycle.edges] at identical
      exact line (Finset.map_injective _ identical)
    · intro same; funext i
      exact decide_eq_decide.mpr (by rw [D.cycle.edges,D.cycle.edges,same])
  let twins := Finset.univ.filter (fun z => D.cycle.label z=D.cycle.label j)
  have mem : j∈twins := Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  have sz : (twins.erase j).card=1 := by rw [Finset.card_erase_of_mem mem,show twins.card=2 from D.cycle.twice _]
  obtain ⟨k,only⟩ := Finset.card_eq_one.mp sz
  have has : k∈twins.erase j := only ▸ Finset.mem_singleton_self k
  obtain ⟨ne,tag⟩ := Finset.mem_erase.mp has
  have match' := (eq k j).mpr (Finset.mem_filter.mp tag).2
  refine ⟨k,ne,fun z h => ?_,fun i => ?_⟩
  · have bz : B j=B z := (decide_eq_decide.mp (named h)).mpr match'.symm
    have fresh : z≠j := by rintro rfl; exact ne ((emb Y).injective (Relations.diagonal _ h.symm).symm)
    have here : z∈twins.erase j := Finset.mem_erase.mpr ⟨fresh,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(eq z j).mp bz.symm⟩⟩
    exact Finset.mem_singleton.mp (only ▸ here)
  · by_cases active : B j i=true
    · exact ((cells j i).mp active).trans ((cells k i).mp (match'.symm ▸ active)).symm
    · exact ((D.palette i j).resolve_left (mt (cells j i).mpr active)).trans
        ((D.palette i k).resolve_left (fun h => active (match' ▸ (cells k i).mpr h))).symm

end QGI.Coherent.LargeOrderCycleMates
