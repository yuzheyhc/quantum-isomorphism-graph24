import ThreeShoreCoordinates

noncomputable section
namespace QGI.Coherent.PinnedShoreSignatures
open SixTenCoordinates SmallUnion StrategyColorLaws Intertwiner Synchrony
open FourTwelveFunctional (source)
open private range from RegionalSixTwelveDispatch
open Classical

variable {n k m l r : Nat} {c d : Fin n → Fin n → Nat}

/-- Equality of two complete rows against one fiber is detected by the internal color. -/
theorem same (law : Laws c d) (Y : Shore c r (Fin k)) (F : Shore c l (Fin m))
    (Z : Shore d r (Fin k)) (T : Shore d l (Fin m)) {i j x y}
    (hit : c (atPoint Y i) (atPoint Y j)=d (atPoint Z x) (atPoint Z y)) :
    (∀ a, c (atPoint Y i) (atPoint F a)=c (atPoint Y j) (atPoint F a)) ↔
    ∀ b, d (atPoint Z x) (atPoint T b)=d (atPoint Z y) (atPoint T b) := by
  obtain ⟨e,h⟩ := law.middle hit
  constructor
  · intro all b
    obtain ⟨s,hs⟩ := e.surjective (atPoint T b)
    obtain ⟨u,hu⟩ := (range F s).mpr ((law.last (h s).1).trans ((congrArg (fun z => d z z) hs).trans (T b).property))
    have a := (h s).1; have b' := law.rev (h s).2
    rw [hs,←hu] at a b'
    exact a.symm.trans ((all u).trans b')
  · intro all a
    obtain ⟨b,hb⟩ := (range T _).mpr ((law.last (h (atPoint F a)).1).symm.trans (F a).property)
    have left := (h (atPoint F a)).1; have right := law.rev (h (atPoint F a)).2
    rw [←hb] at left right
    exact left.trans ((all b).trans right.symm)

variable {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)

theorem coordinates (F : Shore (source G) l (Fin k)) (ξ : cyclic p) (nz : ξ≠0)
    (a : Fin k → Fin n) (fix : ∀ i, U p (atPoint F i) (a i) ξ=ξ) :
    ∃ T : Shore (targetName p) l (Fin k), ∀ i, atPoint T i=a i := by
  have on (i) : U p (atPoint F i) (a i) ξ≠0 := (fix i).symm ▸ nz
  let out (i) : {z : Fin n // targetName p z z=l} := ⟨a i,(DoubledEdges.diag_of_nonzero p (on i)).symm.trans (F i).property⟩
  have inj : Function.Injective out := by
    intro i j eq
    have h : a i=a j := congrArg Subtype.val eq
    have col := RegionalMarkPins.source_name p (fix j) (on i)
    rw [h] at col
    exact F.injective (Subtype.ext (Relations.diagonal (closure G) (col.trans (DoubledEdges.diag_of_nonzero p (on j)).symm)))
  obtain ⟨e,he⟩ := diagonal_names p
  let Z := F.trans (Equiv.subtypeEquiv e (q:=fun z => targetName p z z=l) (fun i => ⟨fun h => (he i).symm.trans h,fun h => (he i).trans h⟩))
  let g := Equiv.ofBijective (fun i => Z.symm (out i)) (Finite.injective_iff_bijective.mp (Z.symm.injective.comp inj))
  exact ⟨g.trans Z,fun i => congrArg Subtype.val (Z.apply_symm_apply (out i))⟩

/-- For at most three names, the names of two representatives distinguish all the classes. -/
theorem representatives {α : Type*} (f : Fin 12 → α) (few : (Finset.univ.image f).card≤3) :
    ∃ i j, ∀ x∈Finset.univ.image f, ∀ y∈Finset.univ.image f,
      (x=f i ↔ y=f i) → (x=f j ↔ y=f j) → x=y := by
  classical
  let V := Finset.univ.image f
  by_cases all : ∀ j, f j=f 0
  · refine ⟨0,0,?_⟩
    rintro x hx y hy _ _
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hy
    exact (all a).trans (all b).symm
  push_neg at all
  obtain ⟨j,diff⟩ := all
  have member (i) : f i∈V := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  let W := (V.erase (f 0)).erase (f j)
  have sj : f j∈V.erase (f 0) := Finset.mem_erase.mpr ⟨diff,member j⟩
  have small : W.card≤1 := by
    simp only [W,Finset.card_erase_of_mem sj,Finset.card_erase_of_mem (member 0)]
    change V.card≤3 at few; omega
  refine ⟨0,j,?_⟩
  intro x hx y hy zero other
  by_cases h : x=f 0
  · exact h.trans (zero.mp h).symm
  by_cases k : x=f j
  · exact k.trans (other.mp k).symm
  exact Finset.card_le_one.mp small x (Finset.mem_erase.mpr ⟨k,Finset.mem_erase.mpr ⟨h,hx⟩⟩)
    y (Finset.mem_erase.mpr ⟨mt other.mpr k,Finset.mem_erase.mpr ⟨mt zero.mpr h,hy⟩⟩)
end QGI.Coherent.PinnedShoreSignatures
