import RegionalEightTwelveComplete

noncomputable section
namespace QGI.Coherent.EightTwelveSignGeometry
open EightTwelveHalf RegionalEightTwelveHalfLaws
abbrev J := Fin 12

def column (j : J) : C := decode (([51,60,85,90,102,105,150,153,165,170,195,204] : List Nat)[j.val]?.getD 0)

private theorem cols : Function.Injective column ∧ Finset.univ.image column=model 4 := by
  unfold Function.Injective
  native_decide

private theorem numbers : (∀ j, (column j).card=4) ∧
    (∀ j, ∃ k, column k=(column j)ᶜ) ∧
    (∀ i x : P, i≠x → crossGram column i x=2 ∨ crossGram column i x=3) ∧
    ∀ i : P, crossGram column i i=6 := by native_decide

private theorem label {a : J → C} (e : Equiv.Perm P)
    (shape : (supports a).image (fun t => t.image e)=model 4) :
    ∃ d : Equiv.Perm J, ∀ j, (a j).image e=column (d j) := by
  have eq : Finset.univ.image (fun j => (a j).image e)=Finset.univ.image column := by
    rw [cols.2,←shape, supports,Finset.image_image]
    rfl
  have hit (j : J) : ∃ k, (a j).image e=column k := by
    have mem : (a j).image e∈Finset.univ.image column := eq ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j)
    obtain ⟨k,_,h⟩ := Finset.mem_image.mp mem
    exact ⟨k,h.symm⟩
  choose d hd using hit
  have surj : Function.Surjective d := by
    intro k
    have mem : column k∈Finset.univ.image (fun j => (a j).image e) := eq.symm ▸ Finset.mem_image_of_mem column (Finset.mem_univ k)
    obtain ⟨j,_,h⟩ := Finset.mem_image.mp mem
    exact ⟨j,cols.1 ((hd j).symm.trans h)⟩
  exact ⟨Equiv.ofBijective d (Finite.surjective_iff_bijective.mp surj),hd⟩

theorem geometric {a : J → C} (e : Equiv.Perm P)
    (shape : (supports a).image (fun t => t.image e)=model 4) :
    Function.Injective a ∧ (∀ j, ∃ k, a k=(a j)ᶜ) ∧
    (∀ i x : P, i≠x → crossGram a i x=2 ∨ crossGram a i x=3) ∧
    (∀ i : P, crossGram a i i=6) := by
  obtain ⟨d,hd⟩ := label e shape
  have hit (j i) : i∈a j ↔ e i∈column (d j) := by rw [←hd]; simp
  have gram (i x) : crossGram a i x=crossGram column (e i) (e x) := by
    unfold crossGram
    apply Finset.card_bij' (fun j _ => d j) (fun k _ => d.symm k)
    · intro j h; simpa only [Finset.mem_filter,Finset.mem_univ,true_and,←hit] using h
    · intro k h
      obtain ⟨j,rfl⟩ := d.surjective k
      simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Equiv.symm_apply_apply,←hit] using h
    · intro j _; exact d.symm_apply_apply j
    · intro k _; exact d.apply_symm_apply k
  refine ⟨fun i j h => d.injective (cols.1 ((hd i).symm.trans ((congrArg (fun t : C => t.image e) h).trans (hd j)))),?_,?_,?_⟩
  · intro j
    obtain ⟨k,h⟩ := numbers.2.1 (d j)
    refine ⟨d.symm k,?_⟩
    ext i
    simp only [Finset.mem_compl,hit,Equiv.apply_symm_apply,h]
  · intro i x ne; rw [gram]; exact numbers.2.2.1 _ _ (fun h => ne (e.injective h))
  · intro i; rw [gram]; exact numbers.2.2.2 _

theorem zero_iff_complement {s t : C} (hs : s.card=4) (ht : t.card=4) :
    (s∩t).card=0 ↔ t=sᶜ := by
  constructor
  · intro h
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      apply Finset.mem_compl.mpr
      intro mem
      have both := Finset.mem_inter.mpr ⟨mem,hi⟩
      rw [Finset.card_eq_zero.mp h] at both
      exact Finset.not_mem_empty _ both
    · rw [Finset.card_compl,hs,ht]; decide
  · rintro rfl; simp

end QGI.Coherent.EightTwelveSignGeometry
