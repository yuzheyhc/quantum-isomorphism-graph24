import RegionalTetraOperators
import RegionalEightTwelveThin

noncomputable section
namespace QGI.Coherent.RegionalEightTwelveQuotient
open Intertwiner Synchrony StrategyColorLaws SixTenCoordinates
open FourTwelveFunctional (source)
open private sums from Intertwiner
open private range from RegionalSixTwelveDispatch

abbrev Label := Fin 4
abbrev Index := Fin 12

private theorem block_sum {A X Y L : Type} [Semiring A] [Fintype X] [Fintype Y] [DecidableEq L]
    (P : X → Y → A) (row : ∀ x, ∑ y, P x y=1) (col : ∀ y, ∑ x, P x y=1)
    (s t : X → L) (u v : Y → L)
    (sound : ∀ i a j b, P i a*P j b≠0 → (s i=t j ↔ u a=v b)) (x : X) (y : Y) :
    ∑ a∈Finset.univ.filter (fun a => u a=v y), P x a=∑ i∈Finset.univ.filter (fun i => t i=s x), P i y := by
  classical
  let B := Finset.univ.filter (fun a => u a=v y)
  let C := Finset.univ.filter (fun i => t i=s x)
  have right (a) (ha : a∈B) : ∑ i∈C, P x a*P i y=P x a := by
    calc _ = ∑ i, P x a*P i y := Finset.sum_subset (Finset.subset_univ _) (fun i _ out => by
           by_contra h; exact out (Finset.mem_filter.mpr ⟨Finset.mem_univ _,((sound x a i y h).mpr (Finset.mem_filter.mp ha).2).symm⟩))
         _ = _ := by rw [←Finset.mul_sum,col,mul_one]
  have left (i) (hi : i∈C) : ∑ a∈B, P x a*P i y=P i y := by
    calc _ = ∑ a, P x a*P i y := Finset.sum_subset (Finset.subset_univ _) (fun a _ out => by
           by_contra h; exact out (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(sound x a i y h).mp (Finset.mem_filter.mp hi).2.symm⟩))
         _ = _ := by rw [←Finset.sum_mul,row,one_mul]
  calc ∑ a∈B, P x a=∑ a∈B, ∑ i∈C, P x a*P i y := (Finset.sum_congr rfl right).symm
       _ = ∑ i∈C, ∑ a∈B, P x a*P i y := Finset.sum_comm
       _ = ∑ i∈C, P i y := Finset.sum_congr rfl left

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {r : Nat} (Y : Shore (source G) r Index) (Z : Shore (targetName p) r Index)

private def M (i j : Index) := U p (atPoint Y i) (atPoint Z j)

private theorem row (i : Index) : ∑ j, M p Y Z i j=1 := by
  apply LinearMap.ext; intro ξ; rw [LinearMap.sum_apply]
  have eq := RegionalTetraOperators.restrict_sum (atPoint Z) (Subtype.val_injective.comp Z.injective)
    (fun z => U p (atPoint Y i) z ξ) (fun z outside => by
      by_contra h; exact outside ((range Z z).mpr ((DoubledEdges.diag_of_nonzero p h).symm.trans (Y i).property)))
  exact eq.symm.trans (sums p (atPoint Y i) ξ).1

private theorem col (j : Index) : ∑ i, M p Y Z i j=1 := by
  apply LinearMap.ext; intro ξ; rw [LinearMap.sum_apply]
  have eq := RegionalTetraOperators.restrict_sum (atPoint Y) (Subtype.val_injective.comp Y.injective)
    (fun i => U p i (atPoint Z j) ξ) (fun i outside => by
      by_contra h; exact outside ((range Y i).mpr ((DoubledEdges.diag_of_nonzero p h).trans (Z j).property)))
  exact eq.symm.trans (sums p (atPoint Z j) ξ).2

private theorem fixed {I L : Type} [Fintype I] [Fintype L] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (q : I → L → Module.End ℂ K) (nz : ∃ ψ : K, ψ≠0)
    (sum : ∀ i, ∑ a, q i a=1) (idem : ∀ i a, q i a*q i a=q i a) (comm : ∀ i j a b, Commute (q i a) (q j b)) :
    ∃ (ξ : K) (f : I → L), ξ≠0 ∧ ∀ i, q i (f i) ξ=ξ := by
  classical
  have get (s : Finset I) : ∃ ξ : K, ξ≠0 ∧ ∀ i∈s, ∃ a, q i a ξ=ξ := by
    induction s using Finset.induction_on with
    | empty => obtain ⟨ψ,hψ⟩ := nz; exact ⟨ψ,hψ,by simp⟩
    | @insert i s _ ih =>
      obtain ⟨ξ,hξ,old⟩ := ih
      have ht := congrArg (fun e : Module.End ℂ K => e ξ) (sum i)
      simp only [LinearMap.sum_apply,Module.End.one_apply] at ht
      have ex : ∃ a, q i a ξ≠0 := by by_contra! all; exact hξ (ht.symm.trans (Finset.sum_eq_zero fun a _ => all a))
      obtain ⟨a,ha⟩ := ex
      refine ⟨q i a ξ,ha,fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact ⟨a,congrArg (fun e : Module.End ℂ K => e ξ) (idem j a)⟩
      · obtain ⟨b,hb⟩ := old j hj
        exact ⟨b,(congrArg (fun e : Module.End ℂ K => e ξ) (comm j i b a).eq).trans (congrArg (q i a) hb)⟩
  obtain ⟨ξ,hξ,all⟩ := get Finset.univ
  choose f hf using fun i => all i (Finset.mem_univ _)
  exact ⟨ξ,f,hξ,hf⟩

/-- The twelve vertices carry all ordered pairs of distinct four-label values.
The original color equations identify row sums and column sums in both label positions. -/
theorem pins (l t : Index → Label) (onto : ∀ a b, a≠b → ∃ j, l j=a ∧ t j=b)
    (inject : ∀ i j, l i=l j → t i=t j → i=j)
    (first : ∀ i j x y, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z x) (atPoint Z y) → (l i=l j ↔ l x=l y))
    (mixed : ∀ i j x y, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z x) (atPoint Z y) → (l i=t j ↔ l x=t y)) :
    ∃ (ξ : cyclic p) (f : Index → Index), ξ≠0 ∧ ∀ i, U p (atPoint Y i) (atPoint Z (f i)) ξ=ξ := by
  classical
  have sur (i : Label) : ∃ j, l j=i := by
    obtain ⟨b,hb⟩ := (show ∀ a : Label, ∃ b, a≠b by decide) i
    obtain ⟨j,h,_⟩ := onto i b hb
    exact ⟨j,h⟩
  choose s hs using sur
  let P := M p Y Z
  let q (i a : Label) := ∑ z∈Finset.univ.filter (fun z => l z=a), P (s i) z
  have eq {i j x y} (hit : P i x*P j y≠0) := (associated p).mpr (StrategyColors.maps_support p hit)
  have write (i j : Label) (z) (h : l z=j) :
      q i j=∑ x∈Finset.univ.filter (fun x => l x=i), P x z := by
    have E := block_sum P (row p Y Z) (col p Y Z) l l l l (fun i a j b nz => first i j a b (eq nz)) (s i) z
    simpa only [q,h,hs] using E
  have write' (i j : Label) (z) (h : t z=j) :
      q i j=∑ x∈Finset.univ.filter (fun x => t x=i), P x z := by
    have E := block_sum P (row p Y Z) (col p Y Z) l t l t (fun i a j b nz => mixed i j a b (eq nz)) (s i) z
    simpa only [q,h,hs] using E
  have column (w : Index) (s t : Finset Index) : Commute (∑ i∈s, P i w) (∑ j∈t, P j w) := by
    change _*_=_*_
    simp only [Finset.sum_mul,Finset.mul_sum]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro i _
    by_cases ij : i=j
    · subst j; rfl
    · have diff : atPoint Y j≠atPoint Y i := (Subtype.val_injective.comp Y.injective).ne (Ne.symm ij)
      exact (magic_orthogonal p _ _ _ diff).2.trans (magic_orthogonal p _ _ _ (Ne.symm diff)).2.symm
  have comm (i j a b) : Commute (q i a) (q j b) := by
    by_cases ab : a=b
    · subst b; rw [write i a (s a) (hs a),write j a (s a) (hs a)]; exact column _ _ _
    obtain ⟨z,hz,ht⟩ := onto a b ab
    rw [write i a z hz,write' j b z ht]; exact column _ _ _
  have idem (i a) : q i a*q i a=q i a := by
    let B := Finset.univ.filter (fun z => l z=a)
    change (∑ z∈B, P (s i) z)*(∑ z∈B,P (s i) z)=_
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro z hz
    rw [Finset.mul_sum,Finset.sum_eq_single z]
    · exact (restricted_projection p _ _).1
    · intro y _ diff; exact (magic_orthogonal p _ _ _ ((Subtype.val_injective.comp Z.injective).ne (Ne.symm diff))).1
    · exact fun out => (out hz).elim
  have sum (i) : ∑ a, q i a=1 := by
    have E := Finset.sum_fiberwise_of_maps_to (fun j (_ : j∈(Finset.univ : Finset Index)) => Finset.mem_univ (l j)) (fun j => P (s i) j)
    exact E.trans (row p Y Z (s i))
  obtain ⟨ξ,f,nz,hf⟩ := fixed q ⟨⟨p.psi,psi_mem p⟩,fun z => psi_ne_zero p (congrArg Subtype.val z)⟩ sum idem comm
  have probe {x z : Index} (active : P x z ξ≠0) (i : Label) : ∃ j, l j=f i ∧
      source G (atPoint Y x) (atPoint Y (s i))=targetName p (atPoint Z z) (atPoint Z j) := by
    by_contra! missed
    apply active
    calc _ = P x z (q i (f i) ξ) := congrArg (P x z) (hf i).symm
         _ = ∑ j∈Finset.univ.filter (fun j => l j=f i), P x z (P (s i) j ξ) := by simp [q,LinearMap.sum_apply]
         _ = 0 := by
           apply Finset.sum_eq_zero; intro j hj
           have zero : P x z*P (s i) j=0 := by by_contra h; exact missed j (Finset.mem_filter.mp hj).2 (eq h)
           exact congrArg (fun e : Module.End ℂ (cyclic p) => e ξ) zero
  have tags {x z : Index} (act : P x z ξ≠0) : l z=f (l x) ∧ t z=f (t x) := by
    obtain ⟨j,hj,e⟩ := probe act (l x)
    obtain ⟨k,hk,d⟩ := probe act (t x)
    exact ⟨((first _ _ _ _ e).mp (hs _).symm).trans hj,
      ((mixed _ _ _ _ (common_transpose p d)).mp (hs _)).symm.trans hk⟩
  have exists' (x : Index) : ∃ z, P x z ξ≠0 := by
    by_contra! h
    have eq := congrArg (fun e : Module.End ℂ (cyclic p) => e ξ) (row p Y Z x)
    simp only [LinearMap.sum_apply,Module.End.one_apply] at eq
    exact nz (eq.symm.trans (Finset.sum_eq_zero fun z _ => h z))
  choose g hg using exists'
  refine ⟨ξ,g,nz,fun x => ?_⟩
  calc P x (g x) ξ = ∑ j, P x j ξ := (Finset.sum_eq_single (g x) (fun j _ notEq => by
          by_contra h
          exact notEq (inject j (g x) ((tags h).1.trans (tags (hg x)).1.symm) ((tags h).2.trans (tags (hg x)).2.symm)))
          (fun absent => (absent (Finset.mem_univ (g x))).elim)).symm
       _ = ξ := by
         have e := congrArg (fun m : Module.End ℂ (cyclic p) => m ξ) (row p Y Z x)
         simpa only [LinearMap.sum_apply,Module.End.one_apply] using e

end QGI.Coherent.RegionalEightTwelveQuotient

