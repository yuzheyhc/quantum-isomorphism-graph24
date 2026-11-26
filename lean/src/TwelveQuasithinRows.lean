import QuasithinFast
import TwelveRowCensus

namespace QGI.TwelveQuasithin
open RowCensus

def profile (t w : Nat) : Bool :=
  let r := wordDigits 12 w
  r.all (fun a => r.count a≤2) && decide (thinCount r=t)

def options (t : Nat) (rs : List Nat) :=
  if rs.isEmpty then (blockRoots 12).filter (profile t) else fastSwitchRows 12 rs

theorem fromChecks {t : Nat} (nodes : Array Node) (existsRoot : 0<nodes.size)
    (first : (nodes[0]?.getD default).rows=[]) (checks : ∀ i : Fin nodes.size,
      verifiedBy TwelveRowCensus.cells (options t) nodes i.val=true) (m : Matrix 12) (h : Laws m)
    (root : word m 0∈blockRoots 12) (fitsProfile : profile t (word m 0)=true) :
    ∃ a, RowCensus.Iso (TwelveRowCensus.cells a) m := by
  apply census_from TwelveRowCensus.cells nodes existsRoot first (options t)
    (fun mat law rs f pos k hk => by
      have nz := List.length_pos_iff.mp pos
      simpa [options,nz] using fastSwitch_complete mat law rs f pos k hk)
    (fun _ => false) checks (fun _ _ absurd => by cases absurd) m h
  simp [options,root,fitsProfile]

end QGI.TwelveQuasithin
