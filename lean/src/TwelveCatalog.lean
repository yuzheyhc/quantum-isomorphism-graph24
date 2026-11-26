import TwelveHighCensus
import TwelveQuasithin2
import TwelveQuasithin4

namespace QGI.TwelveCatalog
open RowCensus

/-- Every twelve-point homogeneous coherent configuration is isomorphic,
up to renaming basic relations, to a listed matrix. -/
theorem complete (c : Table 12 Nat) (h : Laws c) : ∃ a, RowCensus.Iso (TwelveRowCensus.cells a) c := by
  rcases TwelveHighCensus.catalog_or_remaining c h with done|rest
  · exact done
  obtain ⟨m,hm,⟨p,relabel⟩,root,bound,units⟩ := rest
  have fit (t : Nat) (ht : thinCount (wordDigits 12 (word m 0))=t) : TwelveQuasithin.profile t (word m 0)=true := by
    simp only [TwelveQuasithin.profile,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
    exact ⟨bound,ht⟩
  have hit : ∃ a, RowCensus.Iso (TwelveRowCensus.cells a) m := by
    rcases units with two|four
    · exact TwelveQuasithin.units2 m hm root (fit 2 two)
    · exact TwelveQuasithin.units4 m hm root (fit 4 four)
  obtain ⟨a,e,he⟩ := hit
  exact ⟨a,e.trans p,fun i j x y => (he i j x y).trans (relabel _ _ _ _)⟩

end QGI.TwelveCatalog
