import SixTenCoordinates
import FourTwelveFunctional
import MixedFourSixSix

noncomputable section
namespace QGI.Coherent.FourSixSix

open SixTenCoordinates
open FourTwelveFunctional (source fiber_eq)

abbrev I := Fin 4
abbrev E := Fin 6

def incident (i : I) (j : E) : Prop := QGI.MixedFourSixSix.N i j = 1

private instance (i j) : Decidable (incident i j) := inferInstanceAs (Decidable (_ = (1 : Nat)))

private theorem pin_edge : ∀ a b : I, ∀ j : E, a ≠ b →
    incident a 0 → incident b 0 → incident a j → incident b j → j = 0 := by decide

/-- Two four-point/edge-incidence interfaces force a thin color between the
six-point edge sets. Every intermediate vertex in the four-point fiber is
transported by the middle-vertex bijection supplied by the intersection numbers. -/
theorem single_of_tetrahedra {G : Graph 16} {l u v : Nat}
    (F : Shore (source G) l I) (Y : Shore (source G) u E) (Z : Shore (source G) v E)
    {s t : Nat}
    (fy : ∀ i j, source G (atPoint F i) (atPoint Y j) = s ↔ incident i j)
    (fz : ∀ i j, source G (atPoint F i) (atPoint Z j) = t ↔ incident i j) :
    ∀ z, source G (atPoint Y 0) z = source G (atPoint Y 0) (atPoint Z 0) → z = atPoint Z 0 := by
  let c := source G
  intro z hz
  have dv : c z z = v := ((Relations.end_colors (closure G) hz).2).trans (Z 0).property
  let eZ : {z : V // c z z = v} := ⟨z,dv⟩
  let j := Z.symm eZ
  have posZ : atPoint Z j = z := congrArg Subtype.val (Z.apply_symm_apply eZ)
  obtain ⟨sigma,match'⟩ := (sourceLaws (closure G)).middle hz.symm
  have anchor (i : I) (used : incident i 0) : ∃ x : I,
      atPoint F x = sigma (atPoint F i) ∧ incident x 0 ∧ incident x j := by
    obtain ⟨left,right⟩ := match' (atPoint F i)
    have fixed := (Relations.end_colors (closure G) left).2
    let tF : {z : V // c z z = l} := ⟨_,fixed.symm.trans (F i).property⟩
    let x := F.symm tF
    have coord : atPoint F x = sigma (atPoint F i) := congrArg Subtype.val (F.apply_symm_apply tF)
    refine ⟨x,coord,(fy x 0).mp ?_,(fz x j).mp ?_⟩
    · rw [coord]; exact (Relations.transpose (closure G) left).symm.trans ((fy i 0).mpr used)
    · rw [coord,posZ]; exact right.symm.trans ((fz i 0).mpr used)
  obtain ⟨x,hx,hx0,hxj⟩ := anchor 0 (by decide)
  obtain ⟨y,hy,hy0,hyj⟩ := anchor 1 (by decide)
  have diff : x ≠ y := by
    intro h
    have eq := sigma.injective (hx.symm.trans ((congrArg (atPoint F) h).trans hy))
    exact (by decide : (0 : I) ≠ 1) (F.injective (Subtype.ext eq))
  exact posZ.symm.trans (congrArg (atPoint Z) (pin_edge x y j diff hx0 hy0 hxj hyj))

theorem card_shore {n : Nat} {G : Graph 16} {v : Nat} (Z : Shore (source G) v (Fin n)) (j : Fin n) :
    (fiber G (atPoint Z j)).card = n := by
  let f := fun i : Fin n => (⟨atPoint Z i,(fiber_eq _ _).mpr ((Z i).property.trans (Z j).property.symm)⟩ :
    {x // x ∈ fiber G (atPoint Z j)})
  have inj : Function.Injective f := by
    intro i k eq
    have h : atPoint Z i = atPoint Z k := congrArg (fun x : {x // x ∈ fiber G (atPoint Z j)} => x.val) eq
    exact Z.injective (Subtype.ext h)
  have sur : Function.Surjective f := by
    intro x
    let z : {x : V // source G x x = v} := ⟨x.val,((fiber_eq _ _).mp x.property).trans (Z j).property⟩
    have h : atPoint Z (Z.symm z) = x.val := congrArg (fun x : {x : V // source G x x = v} => x.val) (Z.apply_symm_apply z)
    exact ⟨Z.symm z,Subtype.ext h⟩
  simpa using (Fintype.card_congr (Equiv.ofBijective f ⟨inj,sur⟩)).symm

end QGI.Coherent.FourSixSix