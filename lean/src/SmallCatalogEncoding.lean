import Std

namespace QGI.SmallCatalog

structure Row where
  rank : Nat
  cells : Nat
  places : Nat
  chain : List (Nat × List Nat)
  pairMaps : List Nat
  deriving Inhabited

private def hex (s : String) : Nat := s.foldl (fun w c =>
  w*16 + (if c ≤ '9' then c.toNat-'0'.toNat else c.toNat-'a'.toNat+10)) 0
private def words (s : String) := if s.isEmpty then [] else (s.splitOn ",").map hex
private def layers (s : String) := if s.isEmpty then [] else (s.splitOn "/").map fun item =>
  match item.splitOn ":" with
  | [k,ws] => (k.toNat?.getD 0,words ws)
  | _ => (0,[])
def decode (s : String) : Row :=
  match s.splitOn "|" with
  | [r,m,p,c,w] => ⟨r.toNat?.getD 0,hex m,hex p,layers c,words w⟩
  | _ => default

end QGI.SmallCatalog

