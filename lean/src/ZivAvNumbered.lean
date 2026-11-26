import ZivAvCoreCheck

namespace QGI.ZivAv
open SixteenMapSearch QGI.DoubleEight.Prepared
open private vertex from SixteenMapSearch

set_option maxRecDepth 1000

attribute [local irreducible] raw keyed color cores14

theorem entries : ∀ a : Index,
    (∀ i j : Vertex, color a i j < (raw a).rank) ∧
    (∀ i j : Vertex, vertex (keyed a).colors i.val j.val = color a i j) := by native_decide

def name (a : Index) (x y : Vertex) : Fin (raw a).rank :=
  ⟨color a x y,(entries a).1 x y⟩

end QGI.ZivAv
