import SmallVectorRectangles

noncomputable section
namespace QGI.SmallVectorCells
open Classical
open scoped InnerProductSpace
variable {E X Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [Fintype X] [Fintype Y]
variable {ξ : E} {u : X → Y → E} {c : X → X → Nat} {d : Y → Y → Nat} (D : Data ξ u c d)

include D

/-- When each connected support component of the common-vector table
has at most three points per side, all ordered names lift simultaneously. -/
theorem realize (small : ∀ s, Fintype.card (Src u s)≤3) :
    ∃ e : X ≃ Y, ∀ i j, c i j=d (e i) (e j) := by
  have localMap (s) : ∃ e : Src u s ≃ Tgt u s, ∀ i j, ⟪entry u s i (e i),entry u s j (e j)⟫_ℂ≠0 :=
    SmallVectorOrbits.local_small (small s) (size_eq D s) ξ D.nz (entry u s) (part_row D s) (part_col D s)
      (fun i a b ne => D.ro i.val a.val b.val (fun eq => ne (Subtype.ext eq)))
      (fun a i j ne => D.co a.val i.val j.val (fun eq => ne (Subtype.ext eq)))
  obtain ⟨e,compat⟩ := SmallVectorOrbits.synchronize (entry u) localMap
  let f := (Equiv.sigmaFiberEquiv (left u)).symm.trans ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv (right u)))
  refine ⟨f,fun i j => ?_⟩
  let x : Src u (left u i) := ⟨i,rfl⟩
  let y : Src u (left u j) := ⟨j,rfl⟩
  rcases rectangular D small (left u i) (left u j) with flat|rel
  · exact flat x y (e _ x) (e _ y)
  · exact by_contra (fun ne => compat _ _ rel x y (D.bad _ _ _ _ ne))

/-- It suffices to specify any coordinate partition respected by nonzero
entries whose source classes contain at most three points. -/
theorem of_partition {S : Type*} (f : X → S) (g : Y → S)
    (fixed : ∀ i a, u i a≠0 → f i=g a)
    (small : ∀ s, (Finset.univ.filter (fun i => f i=s)).card≤3) :
    ∃ e : X ≃ Y, ∀ i j, c i j=d (e i) (e j) := by
  obtain ⟨h,hl,_⟩ := constant_on_component f g fixed
  apply realize D
  intro s
  rw [Fintype.card_subtype]
  apply (Finset.card_le_card ?_).trans (small (h s))
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hl i).symm.trans (congrArg h (Finset.mem_filter.mp hi).2)⟩

theorem of_target_partition {S : Type*} (g : Y → S)
    (constant : ∀ i a b, u i a≠0 → u i b≠0 → g a=g b)
    (small : ∀ s, (Finset.univ.filter (fun a => g a=s)).card≤3) :
    ∃ e : X ≃ Y, ∀ i j, c i j=d (e i) (e j) := by
  have each (i : X) : ∃ a, u i a≠0 := by
    by_contra! zero
    exact D.nz ((D.row i).symm.trans (by simp [zero]))
  choose f nonzero using each
  obtain ⟨h,_,hr⟩ := constant_on_component (fun i => g (f i)) g (fun i a nz => constant i _ _ (nonzero i) nz)
  apply realize D
  intro s
  rw [size_eq D s,Fintype.card_subtype]
  apply (Finset.card_le_card ?_).trans (small (h s))
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hr i).symm.trans (congrArg h (Finset.mem_filter.mp hi).2)⟩

end QGI.SmallVectorCells
