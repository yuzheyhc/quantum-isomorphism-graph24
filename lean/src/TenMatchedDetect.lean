import TenMatchedCatalog
import HalfPairOperators

noncomputable section
namespace QGI.Coherent.TenPointMatched
open TenPointCross TenPointCross.MatchedCatalog Intertwiner Synchrony StrategyColorLaws
open SixTenCoordinates (Shore atPoint)
open FourTwelveFunctional (source)
open HalfPair
open private M row col from HalfPairOperators

variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (F : Shore (source G) l V) (Y : Shore (source G) r V)
    (T : Shore (targetName p) l V) (Z : Shore (targetName p) r V)
    (S0 : Pairs F Y v) (D : Pairs T Z v)

theorem fixed_labels (dl : D.left=S0.left)
    (old : ∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T i) (atPoint T j))
    (detect : Detects F S0.left) :
    ∃ (ξ : cyclic p) (f : Equiv.Perm Q) (rep : Q → V), ξ≠0 ∧ (∀ i, S0.left (rep i)=i) ∧
      ∀ s t : Fin n, U p s t ξ≠0 → ∀ i, ∃ x, S0.left x=f i ∧
        source G s (atPoint F (rep i))=targetName p t (atPoint T x) := by
  classical
  choose rep hr using label_onto S0.left_two
  let S (a : Q) := Finset.univ.filter (fun x => S0.left x=a)
  let m := M p F T
  let q (i a : Q) := ∑ x∈S a, m (rep i) x
  have hrow (i) : ∑ a,q i a=1 := by
    have h := Finset.sum_fiberwise_of_maps_to (fun x (_ : x∈(Finset.univ : Finset V)) => Finset.mem_univ (S0.left x)) (fun x => m (rep i) x)
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
    have name := (internal S0 D (SixTenCoordinates.commonLaws p) eq).mpr (by rw [dl]; exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
    exact ne ((hr i).symm.trans (name.trans (hr j)))
  have pair (i j a b) (ab : a≠b) (_other : b≠id a) : Commute (q i a+q i b) (q j a+q j b) := by
    obtain ⟨y,hy⟩ := detect a b ab
    let names := (S a∪S b).image (fun x => source G (atPoint F x) (atPoint F y))
    let side (i : Q) := Finset.univ.filter fun k => source G (atPoint F (rep i)) (atPoint F k)∈names
    have reads (x : V) : source G (atPoint F x) (atPoint F y)∈names ↔ x∈S a∪S b := by
      constructor
      · intro h
        obtain ⟨z,hz,eq⟩ := Finset.mem_image.mp h
        simpa only [S,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] using (hy z x eq).mp
          (by simpa only [S,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] using hz)
      · exact Finset.mem_image_of_mem _
    have write (k) : q k a+q k b=∑ t∈side k,m t y := by
      have dis : Disjoint (S a) (S b) := Finset.disjoint_left.mpr fun _ ha hb =>
        ab ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
      change (∑ x∈S a, m (rep k) x)+(∑ x∈S b, m (rep k) x)=_
      rw [←Finset.sum_union dis]
      apply SmallQuotient.square _ _ (row p F T _) (col p F T _)
      intro x t hit
      have eq := (associated p).mpr (StrategyColors.maps_support p hit)
      have same := eq.trans (old x y).symm
      simp only [side,Finset.mem_filter,Finset.mem_univ,true_and,same,reads]
    rw [write i,write j]
    apply Commute.sum_left; intro k _
    apply Commute.sum_right; intro t _
    by_cases kt : k=t
    · subst t; exact Commute.refl _
    have diff : atPoint F t≠atPoint F k := (Subtype.val_injective.comp F.injective).ne (Ne.symm kt)
    change m k y*m t y=m t y*m k y
    exact (magic_orthogonal p (atPoint T y) _ _ (Ne.symm diff)).2.trans (magic_orthogonal p (atPoint T y) _ _ diff).2.symm
  obtain ⟨ξ,f,nz,fix⟩ := SmallQuotient.fixed_classes q
    ⟨⟨p.psi,psi_mem p⟩,fun h => psi_ne_zero p (congrArg Subtype.val h)⟩ hrow idem column
    (SmallQuotient.commutes q hrow idem orth column id pair)
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

end QGI.Coherent.TenPointMatched
