import DoubleEightPrepared

namespace QGI.DoubleEight.Prepared
open SixteenMapSearch
open private atN from SixteenMapSearch
open private Table Table.trans tab stages stage_congr from DoubleEightPrepared

/-- Keys computed intrinsically from the multiplication table can be used
by the same complete palette search for configurations of other orders. -/
def intrinsicKeys (s : Scheme) : Scheme :=
  {s with keys := (stages (tab s) 1).toArray}

theorem mem_intrinsic (s : Scheme) (e : Equiv.Perm (Fin s.rank))
    (bounds : ∀ k : Fin s.rank, transposeName s k.val < s.rank)
    (tr : ∀ i j : Fin s.rank, transposeName s i.val = j.val ↔ transposeName s (e i).val = (e j).val)
    (mul : ∀ k i j : Fin s.rank, coefficient s k.val i.val j.val =
      coefficient s (e k).val (e i).val (e j).val) :
    List.ofFn (fun i => (e i).val) ∈ enumeratedMaps (intrinsicKeys s) (intrinsicKeys s) := by
  have rev (i : Fin s.rank) : e (Table.trans (tab s) i) = Table.trans (tab s) (e i) := by
    apply Fin.ext
    simp only [tab,dif_pos (bounds i),dif_pos (bounds (e i))]
    exact ((tr i ⟨_,bounds i⟩).mp rfl).symm
  apply mem_of_palette_equiv (intrinsicKeys s) (intrinsicKeys s) e _ tr mul
  intro i
  have h := stage_congr (tab s) (tab s) e rev mul 1 i
  simpa [intrinsicKeys,refinedKey,atN,Vector.get,Vector.size_toArray] using h

end QGI.DoubleEight.Prepared
