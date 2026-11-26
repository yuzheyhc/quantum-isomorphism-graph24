import ZivAvNumbered

namespace QGI.ZivAv
open SixteenMapSearch QGI.DoubleEight.Prepared
attribute [local irreducible] raw keyed color cores14
private def positions (input : Nat × Nat) : Array (Vertex × Vertex) := Id.run do
  let mut spots := Array.replicate 256 (0,0)
  for x in List.finRange 14 do
    for y in List.finRange 14 do
      let cell := (input.2 >>> (8*(14*x.val+y.val))) % 256
      spots := spots.set! cell (x,y)
  return spots

private def allPositions := cores14.map positions

def atName (a : Index) (k : Fin (raw a).rank) : Vertex × Vertex :=
  ((allPositions[a.val]?.getD #[])[k.val]?).getD (0,0)

theorem locations : ∀ a : Index, ∀ k : Fin (raw a).rank,
    name a (atName a k).1 (atName a k).2 = k ∧
    transposeName (raw a) k.val = (name a (atName a k).2 (atName a k).1).val := by native_decide

theorem onto (a : Index) (k : Fin (raw a).rank) : ∃ x y, name a x y=k :=
  ⟨_,_,(locations a k).1⟩

end QGI.ZivAv
