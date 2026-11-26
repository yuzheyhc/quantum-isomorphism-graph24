import SmallShoreRealization

noncomputable section
namespace QGI.Coherent.PartialFunctional

open StrategyColorLaws
abbrev source {n : Nat} (G : Graph n) := Relations.color (closure G)

/-- A prescribed source middle vertex has a corresponding target realization
whenever both endpoint colors have the same intersection counts. -/
theorem middle {n : Nat} (c d : Fin n → Fin n → Nat) {i j x y : Fin n}
    (laws : ∀ s t, count c s t i j = count d s t x y) (k : Fin n) :
    ∃ z, c i k = d x z ∧ c k j = d z y := by
  classical
  have eq := laws (c i k) (c k j)
  simp only [count,Finset.sum_boole] at eq
  have pos := Finset.card_pos.mpr (show (Finset.univ.filter (fun z => c i z=c i k ∧ c z j=c k j)).Nonempty from
    ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl,rfl⟩⟩)
  obtain ⟨z,h⟩ := Finset.card_pos.mp (pos.trans_eq eq)
  exact ⟨z,(Finset.mem_filter.mp h).2.1.symm,(Finset.mem_filter.mp h).2.2.symm⟩

theorem extend {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {I X : Type} (u : X → Fin n) (hu : Function.Injective u)
    (a b : I → Fin n) (named : ∀ i j, source G (a i) (a j) = targetName p (b i) (b j))
    (cover : ∀ x : X, ∃ i, ∀ z, source G (a i) z = source G (a i) (u x) → z=u x) :
    ∃ f : X → Fin n, Function.Injective f ∧ (∀ x y, source G (u x) (u y) = targetName p (f x) (f y)) ∧
      ∀ i x, a i = u x → f x = b i := by
  let c := source G
  let d := targetName p
  have forward {i j x y} (eq : c i j=d x y) (k : Fin n) := middle c d (fun s t => common_products p s t eq) k
  have backward {i j x y} (eq : c i j=d x y) (k : Fin n) := middle d c (fun s t => (common_products p s t eq).symm) k
  choose index unique using cover
  have pick (x : X) : ∃ v, c (a (index x)) (u x) = d (b (index x)) v := by
    obtain ⟨v,h,_⟩ := forward (named (index x) (index x)) (u x)
    exact ⟨v,h⟩
  choose f hf using pick
  have toAnchor (x : X) (j : I) : c (u x) (a j) = d (f x) (b j) := by
    obtain ⟨z,h,k⟩ := backward (named (index x) j) (f x)
    exact unique x z (h.symm.trans (hf x).symm) ▸ k.symm
  have allPairs (x y : X) : c (u x) (u y) = d (f x) (f y) := by
    obtain ⟨z,h,k⟩ := backward (toAnchor x (index y)) (f y)
    exact unique y z ((common_transpose p k.symm).trans (hf y).symm) ▸ h.symm
  have inj : Function.Injective f := by
    intro x y same
    apply hu
    have identity := entries p (allPairs x y) (closure H).one_mem (Intertwiner.initial_diagonal p)
    by_contra ne
    simp [Matrix.one_apply,ne,same] at identity
  refine ⟨f,inj,allPairs,fun i x same => ?_⟩
  have identity := entries p (toAnchor x i) (closure H).one_mem (Intertwiner.initial_diagonal p)
  by_contra ne
  simp [Matrix.one_apply,ne,same] at identity

end QGI.Coherent.PartialFunctional
