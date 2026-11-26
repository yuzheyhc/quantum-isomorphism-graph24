import CoherentCoprime
import DiagonalCoordinates
import SmallUnionRealization

noncomputable section
namespace QGI.Coherent.CoprimeBlocks
open Relations StrategyColorLaws

/-- A block is a union of source diagonal colors indicated by a common
label. Only the cardinalities of source blocks and fibers occur here. -/
def blockSize {n : Nat} (G : Graph n) (block : Nat → Nat) (b : Nat) : Nat :=
  (Finset.univ.filter (fun i => block (color (closure G) i i) = b)).card

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Gluing independent blocks of total order at most thirteen realizes
all paired colors. Across different blocks the two fiber sizes must be
coprime. No information about the target partition is required. -/
theorem align_region (p : PerfectStrategy G H K) (active : Nat → Prop) (block : Nat → Nat)
    (small : ∀ b, blockSize G block b ≤ 13)
    (apart : ∀ x y, active (color (closure G) x x) → active (color (closure G) y y) →
      block (color (closure G) x x) ≠ block (color (closure G) y y) →
      ∀ i ∈ fiber G x, ∀ j ∈ fiber G y, color (closure G) i j = color (closure G) x y) :
    ∃ e : Equiv.Perm (Fin n), (∀ i, color (closure G) i i = targetName p (e i) (e i)) ∧
      ∀ i j, active (color (closure G) i i) → active (color (closure G) j j) →
        color (closure G) i j = targetName p (e i) (e j) := by
  classical
  obtain ⟨base,diag⟩ := DiagonalCoordinates.align p
  let c := color (closure G)
  let d := targetName p
  let zone := fun i => block (c i i)
  let region := fun t => {i : Fin n // zone i = t}
  have combine (t : Nat) : ∃ h : Equiv.Perm (region t),
      ∀ x y : region t, c x.val y.val = d (base (h x).val) (base (h y).val) := by
    let k := Fintype.card (region t)
    by_cases positive : 0 < k
    · let u : Fin k ≃ region t := (Fintype.equivFin _).symm
      let f := fun j => (u j).val
      have sf (z) : (∃ i, f i = z) ↔ block (c z z) = t := by
        refine ⟨?_,fun h => ⟨u.symm ⟨z,h⟩,congrArg Subtype.val (u.apply_symm_apply _)⟩⟩
        rintro ⟨i,rfl⟩; exact (u i).property
      have sg (z) : (∃ i, base (f i) = z) ↔ block (d z z) = t := by
        obtain ⟨x,rfl⟩ := base.surjective z
        have aligned : c x x = d (base x) (base x) := diag x
        simpa only [base.injective.eq_iff,←aligned] using sf x
      have size : k ≤ 13 := by simpa [k,region,zone,c,Fintype.card_subtype,blockSize] using small t
      have fi : Function.Injective f := fun _ _ h => u.injective (Subtype.ext h)
      obtain ⟨m,hm⟩ := SmallUnion.realize p positive size (fun a => block a = t) f (base ∘ f) fi
        (base.injective.comp fi) sf sg
      refine ⟨u.symm.trans (m.trans u),?_⟩
      intro x y
      obtain ⟨i,rfl⟩ := u.surjective x
      obtain ⟨j,rfl⟩ := u.surjective y
      simpa only [Equiv.trans_apply,Equiv.symm_apply_apply] using hm i j
    · refine ⟨Equiv.refl _,fun x => ?_⟩
      exact (positive (Fintype.card_pos_iff.mpr ⟨x⟩)).elim
  choose h rel using combine
  let b := Equiv.sigmaFiberEquiv zone
  let e := b.symm.trans ((Equiv.sigmaCongrRight h).trans (b.trans base))
  have ev (t : Nat) (i : region t) : e (b ⟨t,i⟩) = base (h t i).val := by
    simp only [e,Equiv.trans_apply,Equiv.symm_apply_apply]; rfl
  refine ⟨e,?_,?_⟩
  · intro i
    obtain ⟨⟨s,x⟩,rfl⟩ := b.surjective i
    rw [ev]; exact rel s x x
  intro i j ai aj
  obtain ⟨⟨s,x⟩,rfl⟩ := b.surjective i
  obtain ⟨⟨t,y⟩,rfl⟩ := b.surjective j
  rw [ev,ev]
  change c x.val y.val = d (base (h s x).val) (base (h t y).val)
  by_cases st : s = t
  · subst t; exact rel s x y
  · obtain ⟨i,j,hit⟩ := StrategyColors.exists_source p (base (h s x).val) (base (h t y).val)
    have hc := (associated p).mpr (StrategyColors.maps_support p hit)
    obtain ⟨di,dj⟩ := SmallShore.endpoints p hc
    have dx : c i i = c x.val x.val := di.trans (rel s x x).symm
    have dy : c j j = c y.val y.val := dj.trans (rel t y y).symm
    have uniform := apart x.val y.val ai aj (fun bad => st (x.property.symm.trans (bad.trans y.property)))
    have ix : i ∈ fiber G x.val := mem_fiber.mpr ((same _ _ _ _ _).mp dx)
    have jy : j ∈ fiber G y.val := mem_fiber.mpr ((same _ _ _ _ _).mp dy)
    exact (uniform i ix j jy).symm.trans hc

theorem realize_uniform (p : PerfectStrategy G H K) (block : Nat → Nat)
    (small : ∀ b, blockSize G block b ≤ 13)
    (apart : ∀ x y, block (color (closure G) x x) ≠ block (color (closure G) y y) →
      ∀ i ∈ fiber G x, ∀ j ∈ fiber G y, color (closure G) i j = color (closure G) x y) :
    ∃ e : Equiv.Perm (Fin n), ∀ i j, color (closure G) i j = targetName p (e i) (e j) := by
  obtain ⟨e,_,he⟩ := align_region p (fun _ => True) block small (fun x y _ _ => apart x y)
  exact ⟨e,fun i j => he i j trivial trivial⟩

theorem realize (p : PerfectStrategy G H K) (block : Nat → Nat)
    (small : ∀ b, blockSize G block b ≤ 13)
    (apart : ∀ x y, block (color (closure G) x x) ≠ block (color (closure G) y y) →
      (fiber G x).card.Coprime (fiber G y).card) :
    ∃ e : Equiv.Perm (Fin n), ∀ i j, color (closure G) i j = targetName p (e i) (e j) :=
  realize_uniform p block small (fun x y h _ hi _ hj =>
    CoprimeFibers.monochromatic G x y (apart x y h) hi hj)

theorem isomorphic_of_small_blocks (block : Nat → Nat) (small : ∀ b, blockSize G block b ≤ 13)
    (apart : ∀ x y, block (color (closure G) x x) ≠ block (color (closure G) y y) →
      (fiber G x).card.Coprime (fiber G y).card) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,g,ip,_,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  obtain ⟨e,he⟩ := realize p block small apart
  exact ⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (he i j)⟩

end QGI.Coherent.CoprimeBlocks
