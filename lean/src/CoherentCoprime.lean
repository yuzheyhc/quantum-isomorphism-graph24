import StrategyColorLaws
import FiberRectangles

noncomputable section
namespace QGI.Coherent.CoprimeFibers
open Relations FiberRectangles

variable {n : Nat} (G : Graph n)
abbrev col := Relations.color (closure G)

private theorem fiber_iff (i x : Fin n) : i ∈ fiber G x ↔ col G i i = col G x x :=
  mem_fiber.trans (same _ _ _ _ _).symm

private theorem row_sum (a b i j : Fin n) (h : col G i i = col G j j) :
    (∑ z, if col G i z = col G a b then 1 else 0 : Nat) =
      ∑ z, if col G j z = col G a b then 1 else 0 := by
  have pair (i z : Fin n) : (col G i z = col G a b ∧ col G z i = col G b a) ↔
      col G i z = col G a b := ⟨And.left,fun eq => ⟨eq,transpose _ eq⟩⟩
  simpa only [pair] using products (closure G) (col G a b) (col G b a) i i j j h

private theorem restrict_row {b : Nat} {right : Fin b → Fin n} {y : Fin n}
    (embedded : Function.Injective right) (onto : ∀ j, (∃ t, right t = j) ↔ j ∈ fiber G y)
    (i a : Fin n) (t₀ : Fin b) :
    degree (fun t => decide (col G i (right t) = col G a (right t₀))) =
      ∑ j, if col G i j = col G a (right t₀) then 1 else 0 := by
  classical
  let v := fun j => if col G i j = col G a (right t₀) then 1 else 0
  have eq : (∑ t, v (right t)) = ∑ j, v j := by
    apply Fintype.sum_of_injective right embedded _ _ _ (fun _ => rfl)
    intro j outside
    have ne : col G i j ≠ col G a (right t₀) := by
      intro h
      apply outside
      apply (onto j).mpr
      exact (fiber_iff G j y).mpr (((end_colors _ h).2).trans ((fiber_iff G _ _).mp ((onto _).mp ⟨t₀,rfl⟩)))
    simp [v,ne]
  simpa [v,degree] using eq

/-- Each occurring cross color has constant valency at the source and at
the target. The fibers can occur inside an arbitrarily large graph. -/
theorem biregular {a b : Nat} {x y : Fin n} {f : Fin a → Fin n} {g : Fin b → Fin n}
    (fi : Function.Injective f) (gi : Function.Injective g)
    (sf : ∀ z, (∃ i, f i = z) ↔ z ∈ fiber G x) (sg : ∀ z, (∃ i, g i = z) ↔ z ∈ fiber G y) :
    BiregularColors (fun i j => col G (f i) (g j)) := by
  intro v
  by_cases used : ∃ i j, col G (f i) (g j) = v
  · obtain ⟨i,j,rfl⟩ := used
    have rows (i' : Fin a) := restrict_row G gi sg (f i') (f i) j
    have cols (j' : Fin b) := restrict_row G fi sf (g j') (g j) i
    have sameF (i' : Fin a) := ((fiber_iff G _ _).mp ((sf _).mp ⟨i',rfl⟩)).trans
      ((fiber_iff G _ _).mp ((sf _).mp ⟨i,rfl⟩)).symm
    have sameG (j' : Fin b) := ((fiber_iff G _ _).mp ((sg _).mp ⟨j',rfl⟩)).trans
      ((fiber_iff G _ _).mp ((sg _).mp ⟨j,rfl⟩)).symm
    refine ⟨_,(∑ z, if col G (g j) z = col G (g j) (f i) then 1 else 0 : Nat),
      fun i' => (rows i').trans (row_sum G _ _ _ _ (sameF i')),fun j' => ?_⟩
    have rev (u : Fin a) : (col G (f u) (g j') = col G (f i) (g j)) ↔
        col G (g j') (f u) = col G (g j) (f i) := ⟨transpose _,transpose _⟩
    simp_rw [rev]
    exact (cols j').trans (row_sum G _ _ _ _ (sameG j'))
  · push_neg at used
    exact ⟨0,0,fun i => by simp [degree,used],fun j => by simp [degree,used]⟩

/-- Two coherent fibers of coprime cardinalities carry just one forward
color. The statement is about actual vertices in the original graph. -/
theorem monochromatic (x y : Fin n) (cop : (fiber G x).card.Coprime (fiber G y).card)
    {i j : Fin n} (hi : i ∈ fiber G x) (hj : j ∈ fiber G y) :
    col G i j = col G x y := by
  classical
  let S := fiber G x
  let T := fiber G y
  let e : Fin S.card ≃ {u // u ∈ S} := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  let t : Fin T.card ≃ {u // u ∈ T} := (Fintype.equivFinOfCardEq (Fintype.card_coe T)).symm
  let f := fun k => (e k).val
  let g := fun k => (t k).val
  have sf (u) : (∃ k, f k = u) ↔ u ∈ fiber G x := by
    refine ⟨?_,fun h => ⟨e.symm ⟨u,h⟩,congrArg Subtype.val (e.apply_symm_apply _)⟩⟩
    rintro ⟨k,rfl⟩; exact (e k).property
  have sg (u) : (∃ k, g k = u) ↔ u ∈ fiber G y := by
    refine ⟨?_,fun h => ⟨t.symm ⟨u,h⟩,congrArg Subtype.val (t.apply_symm_apply _)⟩⟩
    rintro ⟨k,rfl⟩; exact (t k).property
  have regular := biregular G (fun _ _ h => e.injective (Subtype.ext h))
    (fun _ _ h => t.injective (Subtype.ext h)) sf sg
  obtain ⟨i',hi'⟩ := (sf _).mpr hi
  obtain ⟨j',hj'⟩ := (sg _).mpr hj
  obtain ⟨x',hx'⟩ := (sf _).mpr ((fiber_iff G _ _).mpr rfl)
  obtain ⟨y',hy'⟩ := (sg _).mpr ((fiber_iff G _ _).mpr rfl)
  rw [←hi',←hj',←hx',←hy']
  exact color_constant_of_coprime regular cop x' y' i' j'

end QGI.Coherent.CoprimeFibers
