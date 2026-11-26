import Padding
import Upper24Hilbert

namespace QGI

/-- Adding isolated vertices extends the order-23 lower bound to all smaller orders. -/
theorem lower_from_order23 {n : Nat} (hn : n ≤ 23) (lower : NoSeparation 23) :
    NoSeparation n := by
  intro G H q
  by_contra notIso
  obtain ⟨G', H', q', notIso'⟩ := Padding.promote_le hn ⟨G, H, q, notIso⟩
  exact notIso' (lower G' H' q')

/-- The 24-vertex witness and the order-23 lower bound imply minimality. -/
theorem minimum24_from_lower23 (lower : NoSeparation 23) : ExactMinimum 24 :=
  Padding.exactMinimum24_iff.mpr ⟨Upper24Hilbert.existsSeparation24, lower⟩

end QGI
