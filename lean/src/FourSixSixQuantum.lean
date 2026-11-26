import FourSixSixGeometry
import SmallUnionRealization

noncomputable section
namespace QGI.Coherent.FourSixSix

open SixTenCoordinates StrategyColorLaws
open FourTwelveFunctional (source fiber_eq)

/-- Once a basis relation between a retained vertex and the excluded fiber
has row degree one, all three fibers glue to a single point bijection.
The complement can have any number of fibers and arbitrary internal colors. -/
theorem isomorphic_of_thin {G H : Graph 16} (a b : V) (apart : a ∉ fiber G b)
    (pos : 0 < 16-(fiber G b).card) (small : 16-(fiber G b).card ≤ 13)
    (single : ∀ z, source G a z = source G a b → z = b)
    (quantum : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,g,ip,_,⟨p⟩⟩ := quantum
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  obtain ⟨e,he⟩ := SmallUnion.erase_of_column_one p a b apart pos small single
  exact ⟨⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun x y => common_edge p (he x y)⟩⟩

/-- For 4+6+6, this includes every configuration with a perfect matching
among the named relations between the two six-point fibers. -/
theorem isomorphic_of_six_matching {G H : Graph 16} (a b : V) (apart : a ∉ fiber G b)
    (six : (fiber G b).card = 6) (single : ∀ z, source G a z = source G a b → z=b)
    (quantum : QuantumIso G H) : Isomorphic G H :=
  isomorphic_of_thin a b apart (by omega) (by omega) single quantum

/-- The two tetrahedral incidence interfaces alone force an ordinary graph
isomorphism, with no hypotheses on either six-point internal block or on
the colors between the six-point fibers. -/
theorem isomorphic_of_two_tetrahedra {G H : Graph 16} {l u v : Nat}
    (F : Shore (source G) l I) (Y : Shore (source G) u E) (Z : Shore (source G) v E)
    (apart : u ≠ v) {s t : Nat}
    (fy : ∀ i j, source G (atPoint F i) (atPoint Y j) = s ↔ incident i j)
    (fz : ∀ i j, source G (atPoint F i) (atPoint Z j) = t ↔ incident i j)
    (quantum : QuantumIso G H) : Isomorphic G H := by
  apply isomorphic_of_six_matching (atPoint Y 0) (atPoint Z 0) _ (card_shore Z 0)
    (single_of_tetrahedra F Y Z fy fz) quantum
  intro h
  exact apart ((Y 0).property.symm.trans (((fiber_eq _ _).mp h).trans (Z 0).property))

/-- Glue two named small unions of fibers when cross-region adjacency is
determined by the diagonal names of the two endpoints. Any coherent colors
inside either part are allowed. -/
theorem isomorphic_of_uniform_cut {G H : Graph 16} (reg : Nat → Prop)
    (pos₁ : 0 < (SmallUnion.vertices (source G) reg).card)
    (bound₁ : (SmallUnion.vertices (source G) reg).card ≤ 13)
    (pos₂ : 0 < (SmallUnion.vertices (source G) (fun v => ¬ reg v)).card)
    (bound₂ : (SmallUnion.vertices (source G) (fun v => ¬ reg v)).card ≤ 13)
    (uniform : ∀ i j x y : V, reg (source G i i) → ¬ reg (source G j j) →
      source G i i = source G x x → source G j j = source G y y → G.edge i j = G.edge x y)
    (quantum : QuantumIso G H) : Isomorphic G H := by
  classical
  obtain ⟨K,ng,ip,_,⟨p⟩⟩ := quantum
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  let c := source G
  let d := targetName p
  let P := fun x : V => x ∈ SmallUnion.vertices c reg
  let P' := fun x : V => x ∈ SmallUnion.vertices d reg
  let neg := fun v => ¬ reg v
  have cn (x : V) : ¬P x ↔ x ∈ SmallUnion.vertices c neg := by simp [P,neg]
  have dn (x : V) : ¬P' x ↔ x ∈ SmallUnion.vertices d neg := by simp [P',neg]
  obtain ⟨f,hf⟩ := SmallUnion.realize_region p reg pos₁ bound₁
  obtain ⟨b,hb⟩ := SmallUnion.realize_region p neg pos₂ bound₂
  let t : {x // ¬P x} ≃ {x // ¬P' x} :=
    ((Equiv.subtypeEquivRight cn).trans b).trans (Equiv.subtypeEquivRight dn).symm
  have ht (x y : {x // ¬P x}) : c x.val y.val = d (t x).val (t y).val :=
    hb ((Equiv.subtypeEquivRight cn) x) ((Equiv.subtypeEquivRight cn) y)
  let e := ((Equiv.sumCompl P).symm.trans (Equiv.sumCongr f t)).trans (Equiv.sumCompl P')
  have inside (x : V) (h : P x) : e x = (f ⟨x,h⟩).val := by
    simp only [e,Equiv.trans_apply,Equiv.sumCompl_apply_symm_of_pos _ _ h,Equiv.sumCongr_apply,
      Sum.map_inl,Equiv.sumCompl_apply_inl]
    rfl
  have outside (x : V) (h : ¬P x) : e x = (t ⟨x,h⟩).val := by
    simp only [e,Equiv.trans_apply,Equiv.sumCompl_apply_symm_of_neg _ _ h,Equiv.sumCongr_apply,
      Sum.map_inr,Equiv.sumCompl_apply_inr]
    rfl
  have names (x : V) : c x x = d (e x) (e x) := by
    by_cases h : P x
    · rw [inside x h]; exact hf ⟨x,h⟩ ⟨x,h⟩
    · rw [outside x h]; exact ht ⟨x,h⟩ ⟨x,h⟩
  have mixed (i j : V) (hi : P i) (hj : ¬P j) : G.edge i j = H.edge (e i) (e j) := by
    obtain ⟨x,y,h⟩ := StrategyColors.exists_source p (e i) (e j)
    have n := (associated p).mpr (StrategyColors.maps_support p h)
    obtain ⟨a,b⟩ := SmallShore.endpoints p n
    exact (uniform i j x y ((SmallUnion.mem_vertices _ _ _).mp hi)
      (mt (SmallUnion.mem_vertices _ _ _).mpr hj) ((names i).trans a.symm)
      ((names j).trans b.symm)).trans (common_edge p n)
  refine ⟨⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,?_⟩⟩
  intro x y
  by_cases hx : P x <;> by_cases hy : P y
  · rw [inside x hx,inside y hy]; exact common_edge p (hf ⟨x,hx⟩ ⟨y,hy⟩)
  · exact mixed x y hx hy
  · exact (G.symm _ _).trans ((mixed y x hy hx).trans (H.symm _ _))
  · rw [outside x hx,outside y hy]; exact common_edge p (ht ⟨x,hx⟩ ⟨y,hy⟩)

end QGI.Coherent.FourSixSix
