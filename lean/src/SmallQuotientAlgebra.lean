import RegionalEightTwelveQuotient

namespace QGI.Coherent.SmallQuotient
open private commute_cell from DoubledEdges
open private fixed from RegionalEightTwelveQuotient

/-- Sum a compatibility relation once using a source row and once using a target column. -/
theorem square {R I J : Type} [Semiring R] [Fintype I] [Fintype J] (u : I → R) (v : J → R)
    (row : ∑ i, u i=1) (col : ∑ j, v j=1) (s : Finset I) (t : Finset J)
    (compatible : ∀ i j, u i*v j≠0 → (i∈s ↔ j∈t)) : ∑ i∈s,u i=∑ j∈t,v j := by
  classical
  have right (i) (hi : i∈s) : ∑ j∈t, u i*v j=u i := by
    calc _ = ∑ j,u i*v j := Finset.sum_subset (Finset.subset_univ _) (fun j _ no => by by_contra h; exact no ((compatible i j h).mp hi))
         _ = _ := by rw [←Finset.mul_sum,col,mul_one]
  have left (j) (hj : j∈t) : ∑ i∈s,u i*v j=v j := by
    calc _ = ∑ i,u i*v j := Finset.sum_subset (Finset.subset_univ _) (fun i _ no => by by_contra h; exact no ((compatible i j h).mpr hj))
         _ = _ := by rw [←Finset.sum_mul,row,one_mul]
  exact (Finset.sum_congr rfl right).symm.trans (Finset.sum_comm.trans (Finset.sum_congr rfl left))

/-- Pair columns give commutation for all adjacent labels. A single
missing neighbor per label is recovered from the row sum. -/
theorem commutes {I A R : Type} [Fintype A] [DecidableEq A] [Ring R] (q : I → A → R)
    (sum : ∀ i, ∑ a,q i a=1) (idem : ∀ i a,q i a*q i a=q i a)
    (row : ∀ i a b, a≠b → q i a*q i b=0) (col : ∀ a i j, i≠j → q i a*q j a=0)
    (miss : A → A) (pairs : ∀ i j a b, a≠b → b≠miss a → Commute (q i a+q i b) (q j a+q j b)) :
    ∀ i j a b, Commute (q i a) (q j b) := by
  classical
  intro i j a b
  by_cases ij : i=j
  · subst j
    by_cases eq : a=b
    · subst b; exact Commute.refl _
    · exact (row i a b eq).trans (row i b a (Ne.symm eq)).symm
  have good (k : A) (h : k=a ∨ k≠miss a) : Commute (q i a) (q j k) := by
    by_cases ak : a=k
    · subst k; exact (col a i j ij).trans (col a j i (Ne.symm ij)).symm
    exact commute_cell (idem i a) (row i a k ak) (row i k a (Ne.symm ak)) (col a i j ij) (col a j i (Ne.symm ij))
      (col k i j ij) (col k j i (Ne.symm ij)) (pairs i j a k ak (h.resolve_left (Ne.symm ak)))
  by_cases h : b=miss a
  · have split : q j b=1-∑ k∈Finset.univ.erase b, q j k := by
      apply eq_sub_of_add_eq
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ b)).trans (sum j)
    rw [split]
    exact (Commute.one_right _).sub_right (Commute.sum_right _ _ _ (fun k hk => good k (Or.inr (h ▸ Finset.ne_of_mem_erase hk))))
  · exact good b (Or.inr h)

/-- A common set of nonzero coefficients fixes a bijection of the quotient classes. -/
theorem fixed_classes {I E : Type} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (q : I → I → Module.End ℂ E) (nz : ∃ ψ : E, ψ≠0)
    (sum : ∀ i, ∑ a,q i a=1) (idem : ∀ i a,q i a*q i a=q i a)
    (col : ∀ a i j, i≠j → q i a*q j a=0) (comm : ∀ i j a b, Commute (q i a) (q j b)) :
    ∃ ξ : E, ∃ f : Equiv.Perm I, ξ≠0 ∧ ∀ i, q i (f i) ξ=ξ := by
  obtain ⟨ξ,f,ne,fix⟩ := fixed q nz sum idem comm
  have inj : Function.Injective f := by
    intro i j h
    by_contra diff
    have zero := congrArg (fun z : Module.End ℂ E => z ξ) (col (f i) i j diff)
    change q i (f i) (q j (f i) ξ)=0 at zero
    exact ne ((fix i).symm.trans (by rwa [show q j (f i) ξ=ξ from h ▸ fix j] at zero))
  exact ⟨ξ,Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj),ne,fix⟩

end QGI.Coherent.SmallQuotient
