import Lean

namespace QGI

/-- A finite simple undirected graph on the fixed vertex set Fin n. -/
structure Graph (n : Nat) where
  edge : Fin n → Fin n → Bool
  symm : ∀ x y, edge x y = edge y x
  loopless : ∀ x, edge x x = false

/-- A graph isomorphism includes both directions of the underlying bijection. -/
structure Iso {n : Nat} (G H : Graph n) where
  toFun : Fin n → Fin n
  invFun : Fin n → Fin n
  leftInv : ∀ x, invFun (toFun x) = x
  rightInv : ∀ y, toFun (invFun y) = y
  edge_eq : ∀ x y, G.edge x y = H.edge (toFun x) (toFun y)

def Isomorphic {n : Nat} (G H : Graph n) : Prop := Nonempty (Iso G H)

namespace Iso

def trans {n : Nat} {G H J : Graph n} (f : Iso G H) (g : Iso H J) :
    Iso G J where
  toFun x := g.toFun (f.toFun x)
  invFun z := f.invFun (g.invFun z)
  leftInv x := by rw [g.leftInv, f.leftInv]
  rightInv z := by rw [f.rightInv, g.rightInv]
  edge_eq x y := (f.edge_eq x y).trans (g.edge_eq (f.toFun x) (f.toFun y))

def symm {n : Nat} {G H : Graph n} (f : Iso G H) : Iso H G where
  toFun := f.invFun
  invFun := f.toFun
  leftInv := f.rightInv
  rightInv := f.leftInv
  edge_eq x y := by
    simpa only [f.rightInv] using (f.edge_eq (f.invFun x) (f.invFun y)).symm

end Iso

/-- An injective ordered choice of k pairwise nonadjacent vertices. -/
def HasIndependentSet {n : Nat} (G : Graph n) (k : Nat) : Prop :=
  ∃ f : Fin k → Fin n,
    (∀ i j, f i = f j → i = j) ∧
    (∀ i j, i ≠ j → G.edge (f i) (f j) = false)

theorem Iso.mapIndependentSet {n k : Nat} {G H : Graph n}
    (e : Iso G H) (s : HasIndependentSet G k) : HasIndependentSet H k := by
  obtain ⟨f, inj, edgeless⟩ := s
  refine ⟨fun i => e.toFun (f i), ?_, ?_⟩
  · intro i j h
    apply inj i j
    have t := congrArg e.invFun h
    change e.invFun (e.toFun (f i)) = e.invFun (e.toFun (f j)) at t
    simpa only [e.leftInv] using t
  · intro i j h
    exact (e.edge_eq (f i) (f j)).symm.trans (edgeless i j h)

end QGI
