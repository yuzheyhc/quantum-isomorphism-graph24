import ThinRowOrbits

namespace QGI.RowCensus
open Subgroup

/-- Identify a thin configuration with the group of its color-preserving permutations,
with colors represented by quotients of two group elements. -/
theorem thin_quotients {n : Nat} [NeZero n] {c : Table n (Fin n)} (h : Laws c)
    (thin : ∀ i, Function.Injective (c i)) :
    ∃ e : colorGroup c ≃ Fin n, ∀ p q x y,
      p⁻¹*q=x⁻¹*y ↔ c (e p) (e q)=c (e x) (e y) := by
  let eval := fun p : colorGroup c => p.val 0
  have sur : Function.Surjective eval := by
    intro x
    obtain ⟨p,hp⟩ := colorGroup_moves h thin x
    exact ⟨p⁻¹,p.val.symm_apply_eq.mpr hp.symm⟩
  have bij := sur.bijective_of_nat_card_le (by simp [colorGroup_card h thin])
  let e := Equiv.ofBijective eval bij
  have diff (p q : colorGroup c) : c (e p) (e q)=c 0 (e (p⁻¹*q)) := by
    have eq := (p⁻¹).property (p.val 0) (q.val 0)
    simpa [e,eval,Equiv.Perm.mul_apply] using eq.symm
  exact ⟨e,fun p q x y => by rw [diff,diff]; exact ((thin 0).comp e.injective).eq_iff.symm⟩

abbrev FourThree := Fin 4 × Fin 3

/-- Sylow gives unique coordinates k*u^b in every group of order twelve,
with k in a fixed subgroup of order four and b=0,1,2. -/
theorem four_three {G : Type} [Group G] [Finite G] (card : Nat.card G=12) :
    ∃ (K : Subgroup G) (f : Fin 4 ≃ K) (u : G) (z : FourThree ≃ G),
      f 0=1 ∧ orderOf u=3 ∧ ∀ a b, z (a,b)=(f a).val*u^b.val := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 2 G := Classical.choice inferInstance
  let K : Subgroup G := P
  have k4 : Nat.card K=4 := by
    have eq := P.card_eq_multiplicity
    rw [card] at eq
    apply eq.trans
    rw [show 12=2*2*3 by decide, Nat.factorization_mul (by decide) (by decide), Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization,Nat.prime_three.factorization,Finsupp.single_apply]
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G:=G) 3 (by rw [card]; decide)
  letI := Fintype.ofFinite K
  let v := Fintype.equivOfCardEq (show Fintype.card (Fin 4)=Fintype.card K by
    rw [Fintype.card_fin,← Nat.card_eq_fintype_card,k4])
  let f := (Equiv.swap 0 (v.symm 1)).trans v
  have f0 : f 0=1 := by simp [f]
  let H := Subgroup.zpowers u
  have cop (x : G) (hk : x∈K) (hh : x∈H) : x=1 := by
    have a := orderOf_dvd_natCard (⟨x,hk⟩ : K)
    have b := orderOf_dvd_natCard (⟨x,hh⟩ : H)
    rw [← Subgroup.orderOf_coe,k4] at a
    rw [← Subgroup.orderOf_coe,show Nat.card H=3 from (Nat.card_zpowers u).trans hu] at b
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (show orderOf x ∣ Nat.gcd 4 3 from Nat.dvd_gcd a b))
  let prodG := fun x : FourThree => (f x.1).val*u^x.2.val
  have inj : Function.Injective prodG := by
    rintro ⟨a,b⟩ ⟨d,j⟩ eq
    change (f a).val*u^b.val=(f d).val*u^j.val at eq
    have e : (f d).val⁻¹*(f a).val=u^j.val*(u^b.val)⁻¹ := by
      calc
        _ = (f d).val⁻¹*((f a).val*u^b.val)*(u^b.val)⁻¹ := by group
        _ = _ := by rw [eq]; group
    have trivial := cop _ (K.mul_mem (K.inv_mem (f d).property) (f a).property)
      (e ▸ H.mul_mem (Subgroup.npow_mem_zpowers _ _) (H.inv_mem (Subgroup.npow_mem_zpowers _ _)))
    have da : d=a := f.injective (Subtype.ext (inv_mul_eq_one.mp trivial))
    subst d
    have equalP := mul_left_cancel eq
    have bj : b=j := Fin.ext (pow_injOn_Iio_orderOf (by simpa [hu] using b.isLt) (by simpa [hu] using j.isLt) equalP)
    simp [bj]
  let z := Equiv.ofBijective prodG (inj.bijective_of_nat_card_le (by simp [card,FourThree]))
  exact ⟨K,f,u,z,f0,hu,fun _ _ => rfl⟩

end QGI.RowCensus
