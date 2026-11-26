import RowBalance
import RowBlockRoots
import data.RowCensus12
import data.ZivAvEightTwelve

namespace QGI.TwelveRowCensus
open RowCensus

def rank (c : Table 12 Nat) :=
  (Finset.univ.image fun z : Fin 12 × Fin 12 => c z.1 z.2).card

def cells (a : Fin 59) : Table 12 Nat := fun i j =>
  (((EightTwelveCatalog.rows12[a.val]?.getD default).cells) >>> (4*(12*i.val+j.val)))%16

private def rootRank (w : Nat) :=
  (Finset.univ.image fun j : Fin 12 => digit 12 w j.val).card

private def certificates := decode raw12
private def options (rs : List Nat) := if rs.isEmpty then
  (blockRoots 12).filter (fun w => rootRank w≤5) else balancedRows 12 rs

set_option maxRecDepth 100000 in
private theorem allNodes : ∀ i : Fin certificates.size, verifiedBy cells options certificates i.val := by native_decide

/-- Every homogeneous twelve-point configuration of rank at most five occurs in the data.
Rank counts the diagonal relation. -/
theorem rank_five (c : Table 12 Nat) (h : Laws c) (bound : rank c≤5) : ∃ a, Iso (cells a) c := by
  obtain ⟨m,p,g,hm,start,acts,names⟩ := normalize_blocks c h
  let palette := Finset.univ.image fun z : Fin 12 × Fin 12 => c z.1 z.2
  have sub : (Finset.univ.image fun j : Fin 12 => digit 12 (word m 0) j.val) ⊆
      palette.image (fun a => (g a).val) := by
    intro y hy
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨_,Finset.mem_image.mpr ⟨(p 0,p j),Finset.mem_univ _,rfl⟩,
      by simp [acts]⟩
  have rankBound : rootRank (word m 0)≤5 := (Finset.card_le_card sub).trans (Finset.card_image_le.trans bound)
  obtain ⟨a,e,iso⟩ := census_from cells certificates (by native_decide) (by native_decide) options
    (fun mat law rs f pos k hk => by
      have nz := List.length_pos_iff.mp pos
      simpa [options,nz] using balanced_complete mat law rs f pos k hk)
    (fun _ => false) (fun i => by simpa using allNodes i) (fun _ _ absurd => by cases absurd) m hm
    (by simp [options,start,rankBound])
  exact ⟨a,e.trans p,fun i j x y => (iso i j x y).trans (names _ _ _ _)⟩

end QGI.TwelveRowCensus
