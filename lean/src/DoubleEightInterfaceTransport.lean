import DoubleEightFixedInterface

namespace QGI.DoubleEight.InterfaceTransport

open ShoreCensus FixedInterface

def CrossIso (a b : Coloring) : Prop :=
  ∃ p q : Equiv.Perm V, Same a (fun i j => b (p i) (q j))

theorem crossIso_trans {a b c : Coloring} (h : CrossIso a b) (g : CrossIso b c) : CrossIso a c := by
  obtain ⟨p,q,h⟩ := h
  obtain ⟨s,t,g⟩ := g
  exact ⟨p.trans s,q.trans t,fun i j x y => (h i j x y).trans (g _ _ _ _)⟩

theorem move_homogeneous {c : Coloring} (h : Homogeneous c) (p : Equiv.Perm V) :
    Homogeneous (fun i j => c (p i) (p j)) := by
  have hd := (h.diagonal (p 0) (p 0)).mpr rfl
  refine ⟨fun i j => ?_, fun _ _ _ _ eq => h.transpose _ _ _ _ eq, ?_⟩
  · rw [hd, h.diagonal, p.injective.eq_iff]
  · intro i j x y eq u v
    have shift (a b : V) :
        intersection (fun i j => c (p i) (p j)) u v a b = intersection c u v (p a) (p b) := by
      exact Equiv.sum_comp p (fun z => if c (p a) z = u ∧ c z (p b) = v then 1 else 0)
    rw [shift, shift]
    exact h.products _ _ _ _ eq u v

theorem move_products {X A : Type} [Fintype X] [DecidableEq A] {m : X → X → A}
    (h : HasIntersectionNumbers m) (e : Equiv.Perm X) : HasIntersectionNumbers (fun i j => m (e i) (e j)) := by
  intro u v i j x y eq
  have shift (a b : X) := Equiv.sum_comp e (fun z => (if m (e a) z = u ∧ m z (e b) = v then 1 else 0 : Nat))
  exact (shift i j).trans ((h u v _ _ _ _ eq).trans (shift x y).symm)

/-- Point maps on both shores suffice to use the 636-row catalog at any
labeling of either shore and with arbitrary original relation names. -/
theorem every_raw (k : Fin 88) (m : V ⊕ V → V ⊕ V → Nat)
    (cross : CrossIso (fun i j => m (.inl i) (.inr j)) (named (Nonuniform.layer k).word))
    (hl : Homogeneous (fun i j => m (.inl i) (.inl j)))
    (hr : Homogeneous (fun i j => m (.inr i) (.inr j)))
    (rectangle : ∀ i j x y, m i j = m x y → (side i, side j) = (side x, side y))
    (rev : ∀ i j x y, m i j = m x y → m j i = m y x) (products : HasIntersectionNumbers m) :
    ∃ (t : Nat) (row : Word), Layers.matrices[t]? = some row ∧ PartitionIso m (Placements.color row) := by
  obtain ⟨p,q,h⟩ := cross
  let e := Equiv.sumCongr p.symm q.symm
  let m' := fun i j => m (e i) (e j)
  have hs (i) : side (e i) = side i := by cases i <;> rfl
  have hc : Same (fun i j => m' (.inl i) (.inr j)) (named (Nonuniform.layer k).word) := by
    intro i j x y
    simpa [m',e] using h (p.symm i) (q.symm j) (p.symm x) (q.symm y)
  obtain ⟨n,w,inList,f,hf⟩ := every_raw_nonuniform k m' hc (move_homogeneous hl p.symm)
    (move_homogeneous hr q.symm) (fun i j x y eq => by simpa only [hs] using rectangle _ _ _ _ eq)
    (fun i j x y => rev (e i) (e j) (e x) (e y)) (move_products products e)
  refine ⟨n,w,inList,e.symm.trans f,fun i j x y => ?_⟩
  simpa [m'] using hf (e.symm i) (e.symm j) (e.symm x) (e.symm y)

theorem every_raw_either (k : Fin 88) (m : V ⊕ V → V ⊕ V → Nat)
    (cross : let c := fun i j => m (.inl i) (.inr j)
      CrossIso c (named (Nonuniform.layer k).word) ∨
      CrossIso (FixedInterface.transpose c) (named (Nonuniform.layer k).word))
    (hl : Homogeneous (fun i j => m (.inl i) (.inl j)))
    (hr : Homogeneous (fun i j => m (.inr i) (.inr j)))
    (rectangle : ∀ i j x y, m i j = m x y → (side i, side j) = (side x, side y))
    (rev : ∀ i j x y, m i j = m x y → m j i = m y x) (products : HasIntersectionNumbers m) :
    ∃ (t : Nat) (row : Word), Layers.matrices[t]? = some row ∧ PartitionIso m (Placements.color row) := by
  rcases cross with direct | dual
  · exact every_raw k m direct hl hr rectangle rev products
  let e := Equiv.sumComm V V
  let n := fun i j => m (e i) (e j)
  have inv (u : V ⊕ V) : side (e u) = !side u := by cases u <;> rfl
  have rc : CrossIso (fun i j => n (.inl i) (.inr j)) (named (Nonuniform.layer k).word) := by
    obtain ⟨p,q,rel⟩ := dual
    exact ⟨p,q,fun i j x y => (Iff.intro (rev _ _ _ _) (rev _ _ _ _)).trans (rel i j x y)⟩
  obtain ⟨a,w,aw,f,hf⟩ := every_raw k n rc hr hl (fun i j x y eq => by
    have h := congrArg (fun p : Bool × Bool => (!p.1,!p.2)) (rectangle _ _ _ _ eq)
    simpa only [inv,Bool.not_not] using h) (fun i j x y => rev (e i) (e j) (e x) (e y))
      (move_products products e)
  refine ⟨a,w,aw,e.symm.trans f,fun i j x y => ?_⟩
  simpa [n] using hf (e.symm i) (e.symm j) (e.symm x) (e.symm y)
end QGI.DoubleEight.InterfaceTransport