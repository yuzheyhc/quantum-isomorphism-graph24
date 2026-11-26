import FourAnchorRigidity
import FourAnchorTetra
import StrategyAlgebraIso

noncomputable section

namespace QGI.Coherent.FourFiberSixteen

/-- Four representatives cover the fibers and, in each fiber, an outgoing
internal color at its representative singles out the other endpoint. This
is the row-valency-one property of a thin cell. -/
def FourThinCells (G : Graph 16) : Prop :=
  ∃ u : Fin 4 → Fin 16,
    (∀ x, ∃ i, x ∈ fiber G (u i)) ∧
    ∀ i, ∀ x ∈ fiber G (u i), ∀ y ∈ fiber G (u i),
      Relations.color (closure G) (u i) y = Relations.color (closure G) (u i) x → y = x

end QGI.Coherent.FourFiberSixteen

namespace QGI.Literature
open Coherent

/-- Fuhlbrück–Köbler–Verbitsky, *Identifiability of Graphs with Small
Color Classes by the Weisfeiler–Leman Algorithm*, Theorem 11.1(2) and
the description of its exceptional configuration (Figure 17, proof of
Theorem 11.1, pp. 62–64; proof of Lemma 8.1, pp. 47–48).
At maximum fiber size at most four, the only nonseparable sixteen-point
type has four fibers, skew-connected with fiber graph K₄. At each fiber
two different determined matchings force the cell to be F₄, the association
scheme with a diagonal and three perfect-match relations. If all fibers
have size at most three separability is already stated in §1.
We use only this structural consequence and ordinary separability of the
remaining types, expressed in the coherent-algebra convention.
https://arxiv.org/pdf/1907.02892 -/
axiom fkv_sixteen_small_cells (G : Graph 16) (small : ∀ x, (fiber G x).card ≤ 4) :
    (∀ (D : CoherentAlgebra 16) (e : AlgebraIso (closure G) D), e.Realized) ∨
    FourFiberSixteen.FourThinCells G

end QGI.Literature

namespace QGI.Coherent.FourFiberSixteen
open StrategyColorLaws

private theorem anchors_of_thin {G : Graph 16} (thin : FourThinCells G) :
    ∃ u, FourAnchor.Determines (FourAnchor.Source G) u := by
  obtain ⟨u,cover,localUnique⟩ := thin
  refine ⟨u,fun x => ?_⟩
  obtain ⟨i,hx⟩ := cover x
  refine ⟨i,fun y same => ?_⟩
  have diag := (Relations.end_colors (closure G) same).2
  have hy : y ∈ fiber G (u i) := mem_fiber.mpr (fun M hM =>
    ((Relations.same _ _ _ _ _).mp diag M hM).trans (mem_fiber.mp hx M hM))
  exact localUnique i x hx y hy same

/-- Every basis color of the given strategy map is induced by one point
permutation. In the exceptional nonseparable case the planar tetrahedron
synchronizes the four thin-cell anchors. -/
theorem realize {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) (small : ∀ x, (fiber G x).card ≤ 4) :
    ∃ e : Equiv.Perm (Fin 16), ∀ i j,
      Relations.color (closure G) i j = targetName p (e i) (e j) := by
  rcases Literature.fkv_sixteen_small_cells G small with separable | thin
  · exact StrategyAlgebra.names_of_realized p (separable _ (StrategyAlgebra.equivalence p))
  · obtain ⟨u,single⟩ := anchors_of_thin thin
    obtain ⟨v,hv⟩ := FourAnchorTetra.synchronize p u
    exact FourAnchor.extend p single hv

/-- For all sixteen-point graphs whose coherent fibers have size at most
four, commuting quantum isomorphism implies graph isomorphism. -/
theorem isomorphic_of_max_four {G H : Graph 16} (small : ∀ x, (fiber G x).card ≤ 4)
    (quantum : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,g,ip,complete,⟨p⟩⟩ := quantum
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := complete
  obtain ⟨e,h⟩ := realize p small
  exact ⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (h i j)⟩

end QGI.Coherent.FourFiberSixteen
