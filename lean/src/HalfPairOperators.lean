import HalfPairTransport
import SmallQuotientAlgebra

noncomputable section
namespace QGI.Coherent.HalfPair
open EightTwelveHalf RegionalEightTwelveStats Intertwiner Synchrony StrategyColorLaws SixTenCoordinates
open FourTwelveFunctional (source)
open private sums from Intertwiner
open private range from RegionalSixTwelveDispatch

section
variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {k r : Nat} (Y : Shore (source G) r (Fin k)) (Z : Shore (targetName p) r (Fin k))

private def M (i j : Fin k) := U p (atPoint Y i) (atPoint Z j)

private theorem row (i : Fin k) : ∑ j, M p Y Z i j=1 := by
  apply LinearMap.ext; intro ξ; rw [LinearMap.sum_apply]
  have eq := RegionalTetraOperators.restrict_sum (atPoint Z) (Subtype.val_injective.comp Z.injective)
    (fun z => U p (atPoint Y i) z ξ) (fun z outside => by
      by_contra h; exact outside ((range Z z).mpr ((DoubledEdges.diag_of_nonzero p h).symm.trans (Y i).property)))
  exact eq.symm.trans (sums p (atPoint Y i) ξ).1

private theorem col (j : Fin k) : ∑ i, M p Y Z i j=1 := by
  apply LinearMap.ext; intro ξ; rw [LinearMap.sum_apply]
  have eq := RegionalTetraOperators.restrict_sum (atPoint Y) (Subtype.val_injective.comp Y.injective)
    (fun i => U p i (atPoint Z j) ξ) (fun i outside => by
      by_contra h; exact outside ((range Y i).mpr ((DoubledEdges.diag_of_nonzero p h).trans (Z j).property)))
  exact eq.symm.trans (sums p (atPoint Z j) ξ).2

end

variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (F : Shore (source G) l (Fin 8)) (Y : Shore (source G) r (Fin 12))
    (T : Shore (targetName p) l (Fin 8)) (Z : Shore (targetName p) r (Fin 12)) (v : Nat)
    (L : Layout (family F Y v)) (D : Transport p L F T (family T Z v))

include D in
theorem vector_labels :
    ∃ (ξ : cyclic p) (f : Equiv.Perm Label) (rep : Label → P), ξ≠0 ∧ (∀ i, L.label (rep i)=i) ∧
      ∀ s t : Fin n, U p s t ξ≠0 → ∀ i, ∃ x, L.label x=f i ∧
        source G s (atPoint F (rep i))=targetName p t (atPoint T x) := by
  classical
  choose rep hr using groups _ L
  let S (a : Label) := Finset.univ.filter (fun x => L.label x=a)
  let m := M p F T
  let z := M p Y Z
  let q (i a : Label) := ∑ x∈S a, m (rep i) x
  have hrow (i) : ∑ a,q i a=1 := by
    have h := Finset.sum_fiberwise_of_maps_to (fun x (_ : x∈(Finset.univ : Finset P)) => Finset.mem_univ (L.label x)) (fun x => m (rep i) x)
    exact h.trans (row p F T (rep i))
  have idem (i a) : q i a*q i a=q i a := by
    change (∑ x∈S a,_)*_=_
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro x hx
    change m (rep i) x*(∑ y∈S a, m (rep i) y)=_
    rw [Finset.mul_sum,Finset.sum_eq_single x]
    · exact (restricted_projection p _ _).1
    · intro y _ diff; exact (magic_orthogonal p _ _ _ ((Subtype.val_injective.comp T.injective).ne (Ne.symm diff))).1
    · exact fun out => (out hx).elim
  have orth (i a b) (ne : a≠b) : q i a*q i b=0 := by
    unfold q; rw [Finset.sum_mul]
    apply Finset.sum_eq_zero; intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero; intro y hy
    have diff : x≠y := by rintro rfl; exact ne ((Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2)
    exact (magic_orthogonal p _ _ _ ((Subtype.val_injective.comp T.injective).ne diff)).1
  have column (a i j) (ne : i≠j) : q i a*q j a=0 := by
    unfold q; rw [Finset.sum_mul]
    apply Finset.sum_eq_zero; intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero; intro y hy
    apply Classical.byContradiction; intro hit
    have eq := (associated p).mpr (StrategyColors.maps_support p hit)
    have name := (D.internal _ _ _ _ eq).mpr ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
    exact ne ((hr i).symm.trans (name.trans (hr j)))
  have pair (i j a b) (ab : a≠b) (miss : b≠omitted a) : Commute (q i a+q i b) (q j a+q j b) := by
    obtain ⟨y,hy⟩ := D.pairColumn a b ab miss
    let side (h : Label) := Finset.univ.filter (fun k => rep h∈family F Y v k)
    have write (h) : q h a+q h b=∑ k∈side h,z k y := by
      have dis : Disjoint (S a) (S b) := Finset.disjoint_left.mpr fun _ ha hb =>
        ab ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
      change (∑ x∈S a, m (rep h) x)+(∑ x∈S b, m (rep h) x)=_
      rw [←Finset.sum_union dis]
      apply SmallQuotient.square _ _ (row p F T _) (col p Y Z _)
      intro x k hit
      have e := common_transpose p ((associated p).mpr (StrategyColors.maps_support p hit))
      have member : x∈family T Z v y ↔ rep h∈family F Y v k := by
        simp only [family,color,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨fun h => e.trans h,fun h => e.symm.trans h⟩
      simpa only [side,S,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] using (hy x).symm.trans member
    rw [write i,write j]
    apply Commute.sum_left; intro k _
    apply Commute.sum_right; intro t _
    by_cases kt : k=t
    · subst t; exact Commute.refl _
    have diff : atPoint Y t≠atPoint Y k := (Subtype.val_injective.comp Y.injective).ne (Ne.symm kt)
    change z k y*z t y=z t y*z k y
    exact (magic_orthogonal p (atPoint Z y) _ _ (Ne.symm diff)).2.trans (magic_orthogonal p (atPoint Z y) _ _ diff).2.symm
  obtain ⟨ξ,f,nz,fix⟩ := SmallQuotient.fixed_classes q
    ⟨⟨p.psi,psi_mem p⟩,fun h => psi_ne_zero p (congrArg Subtype.val h)⟩ hrow idem column
    (SmallQuotient.commutes q hrow idem orth column omitted pair)
  refine ⟨ξ,f,rep,nz,hr,?_⟩
  intro s t active i
  apply Classical.byContradiction; intro missed
  apply active
  calc U p s t ξ = U p s t (q i (f i) ξ) := congrArg (U p s t) (fix i).symm
       _ = ∑ x∈S (f i), U p s t (m (rep i) x ξ) := by simp [q,LinearMap.sum_apply]
       _ = 0 := by
         apply Finset.sum_eq_zero; intro x hx
         have zero : U p s t*m (rep i) x=0 := by
           apply Classical.byContradiction; intro h
           exact missed ⟨x,(Finset.mem_filter.mp hx).2,(associated p).mpr (StrategyColors.maps_support p h)⟩
         exact congrArg (fun e : Module.End ℂ (cyclic p) => e ξ) zero

end QGI.Coherent.HalfPair
