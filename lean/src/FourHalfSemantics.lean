import FourHalfCatalog
import RegionalFourFourEight

noncomputable section
namespace QGI.Coherent.FourHalfSemantics
open QGI.FourHalfCatalog Certificate SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open private bundle from SmallFiberExtension

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (p : PerfectStrategy G H K)

theorem apply_certificate (reg : Nat → Prop) (f g : W → Fin n) (fi : Function.Injective f) (gi : Function.Injective g)
    (src : ∀ z, (∃ i,f i=z) ↔ reg (source G z z)) (tgt : ∀ z, (∃ i,g i=z) ↔ reg (targetName p z z))
    (a : Key) (sw : Bool) (q s : Nat) (phase : Bool) (cert : ∃ r, Supports a sw q s r)
    (names : ∀ i j x y, value a sw q s phase i j=value a sw q s (!phase) x y → source G (f i) (f j)=targetName p (g x) (g y))
    (distinguish : ∀ i j x y, source G (f i) (f j)=targetName p (g x) (g y) →
       value a sw q s phase i j=value a sw q s (!phase) x y ∨ (108≤value a sw q s phase i j ∧ 108≤value a sw q s (!phase) x y)) :
    Realizes p reg := by
  classical
  obtain ⟨r,valid⟩ := cert
  cases r with
  | map pts =>
    obtain ⟨inj,eq⟩ := valid
    let e := Equiv.ofBijective (permPoint pts) (Finite.injective_iff_bijective.mp inj)
    have map : ∃ h : Equiv.Perm W, ∀ i j, source G (f i) (f j)=targetName p (g (h i)) (g (h j)) := by
      cases phase with
      | false => exact ⟨e,fun i j => names _ _ _ _ (eq i j)⟩
      | true =>
        refine ⟨e.symm,fun i j => names _ _ _ _ ?_⟩
        have back := eq (e.symm i) (e.symm j)
        change value a sw q s false (e.symm i) (e.symm j)=value a sw q s true (e (e.symm i)) (e (e.symm j)) at back
        simpa only [Equiv.apply_symm_apply] using back.symm
    obtain ⟨h,hw⟩ := map
    choose k hk using fun x : Region (source G) reg => (src x.val).mpr ((mem_vertices _ _ _).mp x.property)
    obtain ⟨E,hE⟩ := bundle p reg (fun x => g (h (k x))) (fun i j => by simpa only [hk] using hw (k i) (k j))
    exact ⟨E,fun i j => by rw [hE,hE]; simpa only [hk] using hw (k i) (k j)⟩
  | obstruct pat colors =>
    obtain ⟨shape,arity,small,ne⟩ := valid
    have draw : ∃ v, Draws pat v := by
      rcases shape with rfl|rfl
      · exact drawing_of_tetraPrism rfl
      · exact RegionalPlanar.drawing_nearClique
    have h := RegionalPlanar.homCount_region p (k:=20) (by decide) reg f g fi gi src tgt
      (matrix a sw q s phase) (matrix a sw q s (!phase)) rfl rfl pat draw colors arity id (by
        intro i j x y eq c hc
        rw [read,read]; change _=c ↔ _=c
        rcases distinguish i j x y eq with same|⟨h₁,h₂⟩
        · rw [same]
        · have := small c hc; omega)
    rw [List.map_id] at h
    cases phase with
    | false => exact (ne h).elim
    | true => exact (ne h.symm).elim

end QGI.Coherent.FourHalfSemantics
