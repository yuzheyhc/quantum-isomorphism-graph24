import RegionalSixTwelveMatching

noncomputable section
namespace QGI.Coherent.RegionalTetraLayout
open SixTenCoordinates StrategyColorLaws RegionalSixTwelveStats
open RegionalSixTwelveGeometry (Point Family degree)
open FourTwelveCycle (Edge edge ends)
open FourTwelveFunctional (source)
open private star_degree from RegionalSixTwelve

abbrev Face := Fin 4
abbrev Slot := Fin 3

structure Layout {n l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l Point) (Y : Shore c r Right) (v w : Nat) where
  left : Equiv.Perm Point
  right : Face × Slot ≃ Right
  names : ∀ q k e, color F Y (right (q,k)) (left e)=if q∈edge e then v else w

private theorem equal_degree (f : Family) (size : f.card=4) (wt : ∀ s∈f, s.card=3) (reg : RegionalSixTwelveGeometry.Regular f) :
    ∀ i, degree f i=2 := by
  have row (i : Point) : degree f i=∑ s∈f, if i∈s then 1 else 0 := by simp [degree]
  have total : ∑ i : Point, degree f i=∑ s∈f, s.card := by
    simp_rw [row]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro s _; simp
  have h := total.trans (Finset.sum_congr rfl wt : (∑ s∈f, s.card)=∑ _s∈f, 3)
  have constant (i : Point) : degree f i=degree f 0 := reg i
  simp only [constant,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,size] at h
  exact fun i => (reg i).trans (by omega)

theorem make {n l r : Nat} {c : Fin n → Fin n → Nat} (law : Laws c c) (F : Shore c l Point) (Y : Shore c r Right)
    {v w : Nat} (palette : ∀ j i, color F Y j i=v ∨ color F Y j i=w)
    (weight : ∀ j, (family F Y v j).card=3)
    (four : (support (family F Y v)).card=4)
    (inter : ∀ s∈support (family F Y v), ∀ t∈support (family F Y v), s≠t → (s∩t).card=1)
    (tripled : ∀ s∈support (family F Y v), mu (family F Y v) s=3) : Nonempty (Layout F Y v w) := by
  classical
  let b := family F Y v
  let f := support b
  let label : Face ≃ RegionalSixTwelve.Member f := Fintype.equivOfCardEq (by rw [Fintype.card_coe,four,Fintype.card_fin])
  let members (q : Face) := {j : Right // b j=(label q).val}
  let each (q : Face) : Slot ≃ members q := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin,Fintype.card_subtype]; exact (tripled _ (label q).property).symm)
  let k : Face × Slot → Right := fun t => (each t.1 t.2).val
  have indexed (q t) : b (k (q,t))=(label q).val := (each q t).property
  have inject : Function.Injective k := by
    rintro ⟨q,s⟩ ⟨t,a⟩ h
    obtain rfl : q=t := label.injective (Subtype.ext (((indexed q s).symm.trans (congrArg b h)).trans (indexed t a)))
    obtain rfl : s=a := (each q).injective (Subtype.ext h)
    rfl
  let right := Equiv.ofBijective k ((Fintype.bijective_iff_injective_and_card k).mpr ⟨inject,by decide⟩)
  have wt (s) (hs : s∈f) : s.card=3 := by obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs; exact weight j
  have deg := equal_degree f four wt (statistics law F Y v).2.2.2
  let hits (i : Point) := Finset.univ.filter fun q : Face => i∈(label q).val
  have count (i : Point) : (hits i).card=2 := by
    have mapped : (hits i).map label.toEmbedding=RegionalSixTwelve.star f i := by
      ext z
      obtain ⟨q,rfl⟩ := label.surjective z
      simp [hits,RegionalSixTwelve.star]
    have h := congrArg Finset.card mapped
    rw [Finset.card_map] at h
    exact h.trans ((star_degree f i).trans (deg i))
  have get (e : Edge) : ∃ i, hits i=edge e := by
    let u := (FourTwelveCycle.ends e).1
    let t := (FourTwelveCycle.ends e).2
    have ne : u≠t := (show ∀ z : Edge, (FourTwelveCycle.ends z).1≠(FourTwelveCycle.ends z).2 by decide) e
    have nr : (label u).val≠(label t).val := fun h => ne (label.injective (Subtype.ext h))
    obtain ⟨i,hi⟩ := Finset.card_pos.mp ((by decide : 0<1).trans_eq
      (inter _ (label u).property _ (label t).property nr).symm)
    refine ⟨i,Eq.symm (Finset.eq_of_subset_of_card_le ?_ ?_)⟩
    · change ({u,t} : Finset Face)⊆hits i
      obtain ⟨x,y⟩ := Finset.mem_inter.mp hi
      exact Finset.insert_subset (Finset.mem_filter.mpr ⟨Finset.mem_univ _,x⟩)
        (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,y⟩))
    · rw [count]; exact (show ∀ z : Edge, 2≤(edge z).card by decide) e
  choose value hv using get
  have mono : Function.Injective value := fun i j h => FourTwelveTypes.edge_inj
    (((hv i).symm.trans (congrArg hits h)).trans (hv j))
  let left := Equiv.ofBijective value (Finite.injective_iff_bijective.mp mono)
  refine ⟨⟨left,right,fun q t e => ?_⟩⟩
  have inc : color F Y (right (q,t)) (left e)=v ↔ q∈edge e := by
    have h : q∈hits (value e) ↔ q∈edge e := by rw [hv e]
    change color F Y (k (q,t)) (value e)=v ↔ q∈edge e
    rw [←h]
    change color F Y (k (q,t)) (value e)=v ↔ q∈hits (value e)
    have hit := indexed q t
    have alt : value e∈b (k (q,t)) ↔ value e∈(label q).val := by rw [hit]
    simpa only [family,b,hits,color,Finset.mem_filter,Finset.mem_univ,true_and] using alt
  split
  · exact inc.mpr ‹_›
  · exact (palette _ _).resolve_left (mt inc.mp ‹_›)

end QGI.Coherent.RegionalTetraLayout

