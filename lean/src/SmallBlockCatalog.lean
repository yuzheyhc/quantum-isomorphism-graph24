import ImprimitiveRankThree
import HomogeneousUnions

namespace QGI.RowCensus
open Homogeneous.Unions (rawTables colorAt)

private def archiveIndex (n d : Nat) := if n=d then 0 else
  if n=16 then (if d=2 then 1 else if d=4 then 2 else 6)
  else (if d=2 then 1 else if d=3 then 2 else if d=6 then 3 else 4)

private def matchesArchive (n : Nat) :=
  (n::blockSizes n).all fun d =>
    let a := archiveIndex n d
    let tables := rawTables n
    decide (a<tables.length ∧ ∀ i j : Fin n, colorAt (tables.getD a #[]) i.val j.val=blockColor d i j)

private theorem checks : matchesArchive 16=true ∧ matchesArchive 18=true := by native_decide

/-- Reconstruct the exact catalog coordinates for the rank-two case and
every imprimitive rank-three case at orders sixteen and eighteen. -/
theorem small_block_catalog {n : Nat} [NeZero n] (hn : n=16 ∨ n=18)
    (c : Table n Nat) (h : Laws c)
    (small : (palette c).card≤2 ∨ ((palette c).card≤3 ∧ Nonempty (Imprimitivity c))) :
    ∃ t∈rawTables n, Iso (fun i j : Fin n => colorAt t i.val j.val) c := by
  have verified : matchesArchive n=true := hn.elim (fun e => e ▸ checks.1) (fun e => e ▸ checks.2)
  have bounds : 16≤n ∧ n≤23 := by rcases hn with rfl|rfl <;> decide
  have choice : ∃ d∈n::blockSizes n, Iso (blockColor d) c := by
    rcases small with low|⟨rank,⟨b⟩⟩
    · exact ⟨n,List.mem_cons_self,rank_two h low⟩
    · obtain ⟨d,mem,iso⟩ := block_models bounds.1 bounds.2 h rank b
      exact ⟨d,List.mem_cons_of_mem _ mem,iso⟩
  obtain ⟨d,mem,iso⟩ := choice
  obtain ⟨existsRow,same⟩ := of_decide_eq_true (List.all_eq_true.mp verified d mem)
  refine ⟨(rawTables n).getD (archiveIndex n d) #[],?_,?_⟩
  · simpa [List.getD_eq_getElem?_getD,existsRow] using (List.getElem_mem (l:=rawTables n) (n:=archiveIndex n d) (h:=existsRow))
  · simpa only [same] using iso

end QGI.RowCensus
