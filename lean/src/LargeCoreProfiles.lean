import CoprimeProfiles
import SmallFiberExtension

namespace QGI.Coherent.LargeCoreProfiles
open Relations CoprimeProfiles StrategyColorLaws SmallUnion

variable {n : Nat} {G H : Graph n}

/-- Every approved size list yields an actual point bijection for every
graph with that profile. The check glues the large fibers first and then
successively reattaches all fibers of at most three vertices. -/
theorem isomorphic {xs : List Nat} (P : Profile G xs) (valid : checkFrom 4 xs = true)
    (q : QuantumIso G H) : Isomorphic G H := by
  classical
  obtain ⟨K,g,ip,_,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  let c := color (closure G)
  let large := fun v => 3 < (vertices c (fun w => w=v)).card
  have size (i : Fin n) : vertices c (fun w => w=c i i) = fiber G i := by
    ext j; exact (mem_vertices _ _ _).trans ((same _ _ _ _ _).trans mem_fiber.symm)
  obtain ⟨b,bound,apart⟩ := grouping 4 P valid
  obtain ⟨h,diag,he⟩ := CoprimeBlocks.align_region p large b bound (fun x y hx hy diff i hi j hj => by
    change 3 < (vertices c (fun w => w=c x x)).card at hx
    change 3 < (vertices c (fun w => w=c y y)).card at hy
    rw [size] at hx hy
    exact CoprimeFibers.monochromatic G x y (apart x y hx hy diff) hi hj)
  have matched (i) : i ∈ vertices c large ↔ h i ∈ vertices (targetName p) large := by
    simp only [mem_vertices]; exact (congrArg large (diag i)).to_iff
  let f := h.subtypeEquiv matched
  have localReal : SmallFiberExtension.Realizes p large :=
    ⟨f,fun i j => he i.val j.val ((mem_vertices _ _ _).mp i.property) ((mem_vertices _ _ _).mp j.property)⟩
  obtain ⟨e,finalMap⟩ := SmallFiberExtension.of_large_region p localReal
  exact ⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (finalMap i j)⟩

def tally (n : Nat) : Nat := ((Routes.enumerate n 1 n).filter (checkFrom 4)).length

set_option maxRecDepth 10000 in
theorem counted : (List.range 8).map (fun i => tally (16+i)) = [210,266,328,407,495,602,724,867] := by
  native_decide

set_option maxRecDepth 10000 in
theorem matches_route : ∀ i : Fin 8, (Routes.enumerate (16+i.val) 1 (16+i.val)).all
    (fun xs => checkFrom 4 xs == decide (Routes.maxCore xs ≤ 13)) = true := by
  native_decide

end QGI.Coherent.LargeCoreProfiles
