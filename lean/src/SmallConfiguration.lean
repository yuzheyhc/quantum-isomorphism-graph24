import DoubleEightFixedInterface

open scoped BigOperators

namespace QGI.Coherent.SmallUnion
abbrev Table (n : Nat) := Fin n → Fin n → Nat

/-- The diagonal is a union of colors, transpose respects colors, and all
intersection numbers are constant on each color. Multiple fibers are allowed. -/
structure Configuration {n : Nat} (c : Table n) : Prop where
  diagonal : ∀ i j x, c i j = c x x → i = j
  reverse : ∀ i j x y, c i j = c x y → c j i = c y x
  products : DoubleEight.FixedInterface.HasIntersectionNumbers c

end QGI.Coherent.SmallUnion
