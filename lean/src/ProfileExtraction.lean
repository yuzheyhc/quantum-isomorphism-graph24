import CoprimeProfiles
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.OfFn

noncomputable section
namespace QGI.Coherent.CoprimeProfiles
open Relations

private theorem fits_of_sorted (xs : List Nat) (l : Nat) (positive : ∀ i ∈ xs, 0 < i)
    (bounded : ∀ i ∈ xs, l ≤ i) (sorted : xs.Pairwise (· ≤ ·)) : Routes.Fits l xs.sum xs := by
  induction xs generalizing l with
  | nil => exact Routes.Fits.nil l
  | cons a t ih =>
    obtain ⟨least,tail⟩ := List.pairwise_cons.mp sorted
    exact Routes.Fits.cons (bounded a (by simp)) (positive a (by simp))
      (ih a (fun i hi => positive i (List.mem_cons_of_mem _ hi)) least tail)

/-- Every graph admits a sorted profile of positive fiber sizes in the partition enumeration. -/
theorem extract {n : Nat} (G : Graph n) : ∃ xs ∈ Routes.enumerate n 1 n, Nonempty (Profile G xs) := by
  classical
  let diag := fun i => color (closure G) i i
  let colors := Finset.univ.image diag
  let N := Fintype.card {v // v ∈ colors}
  let u : Fin N ≃ {v // v ∈ colors} := (Fintype.equivFin _).symm
  let v := fun i : Fin n => (⟨diag i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩ : {v // v ∈ colors})
  let t := fun i => u.symm (v i)
  let size := fun k : Fin N => (Finset.univ.filter (fun i => t i = k)).card
  let perm := Tuple.sort size
  let weight := fun k : Fin N => size (perm k)
  let xs := List.ofFn weight
  have len : xs.length = N := List.length_ofFn
  have onto (k : Fin N) : ∃ i, t i=k := by
    obtain ⟨i,_,eq⟩ := Finset.mem_image.mp (u k).property
    exact ⟨i,u.symm_apply_eq.mpr (Subtype.ext eq)⟩
  have pos (k : Fin N) : 0 < size k := by
    obtain ⟨i,hi⟩ := onto k
    exact Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  have allPos (x) (h : x ∈ xs) : 0 < x := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    exact pos (perm i)
  have sum : xs.sum = n := by
    have total := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n))
      (Finset.univ : Finset (Fin N)) t
    simpa only [xs,List.sum_ofFn,weight,Equiv.sum_comp] using
      (show (∑ k, size k) = n by simpa [size] using total)
  have sorted : xs.Pairwise (· ≤ ·) := List.pairwise_ofFn.mpr fun _ _ h => Tuple.monotone_sort size h.le
  have fits := fits_of_sorted xs 1 allPos allPos sorted
  rw [sum] at fits
  let tag := fun i => Fin.cast len.symm (perm.symm (t i))
  refine ⟨xs,Routes.complete fits n (Routes.length_le_total fits),⟨⟨tag,?_,?_⟩⟩⟩
  · intro i j
    simp only [tag,Fin.cast_inj,Equiv.apply_eq_iff_eq,t,v,Subtype.mk.injEq]
    rfl
  · intro i
    let j := Fin.cast len i
    have posEq (z : Fin n) : tag z = i ↔ t z = perm j := by
      change Fin.cast len.symm (perm.symm (t z)) = i ↔ _
      rw [←Fin.val_inj,show (Fin.cast len.symm (perm.symm (t z))).val = (perm.symm (t z)).val from rfl]
      exact (Fin.val_inj (a := perm.symm (t z)) (b := j)).trans perm.symm_apply_eq
    simp_rw [posEq]
    change size (perm j) = (List.ofFn weight)[i.val]
    rw [List.getElem_ofFn]
    rfl

end QGI.Coherent.CoprimeProfiles
