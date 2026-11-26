import SmallConfiguration

noncomputable section
namespace QGI.Coherent.SmallShore

abbrev Table (n : Nat) := Fin n → Fin n → Nat

/-- A finite homogeneous coherent configuration with specified diagonal name. -/
structure Local {k : Nat} (m : Table k) (d : Nat) : Prop where
  diag : ∀ i j, m i j = d ↔ i = j
  reverse : ∀ i j x y, m i j = m x y → m j i = m y x
  products : DoubleEight.FixedInterface.HasIntersectionNumbers m

theorem Local.configuration {k d : Nat} {c : Table k} (h : Local c d) :
    SmallUnion.Configuration c :=
  ⟨fun i j x eq => (h.diag i j).mp (eq.trans ((h.diag x x).mpr rfl)),
    h.reverse, h.products⟩

end QGI.Coherent.SmallShore

