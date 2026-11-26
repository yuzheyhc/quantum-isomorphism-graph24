import ThreeShoreCoordinates
import FourCycleVectors

noncomputable section
namespace QGI.Coherent.FourSixJointPins
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws Intertwiner Synchrony
open RegionalCycleExtension (emb range_emb)
open FourTwelveFunctional (source)
open private narrow from TwoAnchorUnionGlue
variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)

theorem pinned (F : Shore (source G) l (Fin 4)) (S : Shore (source G) r (Fin 6)) (t : Nat) (m : Equiv.Perm (Fin 6))
    (inc : ∀ i j, source G (atPoint F i) (atPoint S j)=t ↔ FourSixSix.incident i (m j)) :
    ∃ (ξ : cyclic p) (a : Fin 4 → Fin n) (b : Fin 6 → Fin n), ξ≠0 ∧
      (∀ i, U p (atPoint F i) (a i) ξ=ξ) ∧ ∀ j, U p (atPoint S j) (b j) ξ=ξ := by
  let keep := fun w => w=l ∨ w=r
  obtain ⟨e,names⟩ := LargeOrderBlocks.small p keep ((RegionalTwoAnchor.pair_bound F S).trans (by decide))
  let T := F.trans (narrow e names (show keep l from Or.inl rfl))
  let Z := S.trans (narrow e names (show keep r from Or.inr rfl))
  let f (i : Fin 4) : Region (source G) keep := ⟨atPoint F i,(mem_vertices _ _ _).mpr (Or.inl (F i).property)⟩
  let s (i : Fin 6) : Region (source G) keep := ⟨atPoint S i,(mem_vertices _ _ _).mpr (Or.inr (S i).property)⟩
  have both (i j) : source G (atPoint F i) (atPoint S j)=targetName p (atPoint T i) (atPoint Z j) := names (f i) (s j)
  have tetra : ∀ i j : Fin 4, i≠j → ∃ z, ∀ k, FourSixSix.incident k z ↔ k=i ∨ k=j := by unfold FourSixSix.incident; native_decide
  obtain ⟨q,hq⟩ := tetra 0 1 (by decide)
  let j := m.symm q
  have base : targetName p (atPoint T 0) (atPoint Z j)=t := (both 0 j).symm.trans ((inc 0 j).mpr (by
    rw [show m j=q from m.apply_symm_apply q,hq]; exact Or.inl rfl))
  let v := targetName p (atPoint Z j) (atPoint T 0)
  have mark (x z) : targetName p (atPoint Z z) (atPoint T x)=v ↔ FourSixSix.incident x (m z) := by
    rw [←inc, both, ←base]
    exact (target_same p _ _ _ _).trans ((Iff.intro (Relations.transpose _) (Relations.transpose _)).trans (target_same p _ _ _ _).symm)
  obtain ⟨ξ,g,nz,fix⟩ := FourCycleVectors.fixed_of_cycle p (emb F) (emb T) v
    (fun i a _ h => (range_emb T _).mpr ((DoubledEdges.diag_of_nonzero p h).symm.trans (F i).property)) (by
      intro i; refine ⟨i,?_⟩; intro j' ne _
      obtain ⟨w,hw⟩ := tetra i j' ne
      let u := m.symm w
      have mu : m u=w := m.apply_symm_apply _
      refine ⟨atPoint Z u,?_⟩
      ext z
      constructor
      · intro hit
        have raw := (Finset.mem_filter.mp hit).2
        have diag := Relations.end_colors (closure H) ((target_same p _ _ _ _).mp raw)
        obtain ⟨k,rfl⟩ := (range_emb T _).mpr (((target_same p _ _ _ _).mpr diag.2).trans (T 0).property)
        have got := (mark k u).mp raw
        rw [mu,hw] at got
        simpa only [Finset.mem_insert,Finset.mem_singleton] using got.imp (congrArg (emb T)) (congrArg (emb T))
      · intro hz
        rcases Finset.mem_insert.mp hz with hz|hz
        · subst z; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mark i u).mpr (mu ▸ (hw i).mpr (Or.inl rfl))⟩
        · obtain rfl := Finset.mem_singleton.mp hz
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mark j' u).mpr (mu ▸ (hw j').mpr (Or.inr rfl))⟩)
  obtain ⟨b,bfix⟩ := RegionalMarkPins.grow p nz (atPoint F) (fun i => atPoint T (g i)) fix S (by
    intro i u same
    apply m.injective
    apply (show ∀ x y : Fin 6, (∀ z, FourSixSix.incident z x ↔ FourSixSix.incident z y) → x=y by unfold FourSixSix.incident; native_decide)
    intro z; rw [←inc,←inc]; exact (congrArg (·=t) (Relations.transpose _ (same z))).to_iff)
  exact ⟨ξ,_,b,nz,fix,bfix⟩
end QGI.Coherent.FourSixJointPins
