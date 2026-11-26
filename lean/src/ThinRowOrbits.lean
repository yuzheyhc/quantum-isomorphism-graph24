import RowCensus

namespace QGI.RowCensus
variable {n : Nat} [NeZero n]
def colorGroup (c : Table n (Fin n)) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {p | ∀ i j, c (p i) (p j)=c i j}
  one_mem' := by intro i j; rfl
  mul_mem' := by intro a b ha hb i j; exact (ha (b i) (b j)).trans (hb i j)
  inv_mem' := by
    intro a ha i j
    simpa using (ha (a.symm i) (a.symm j)).symm

theorem colorGroup_moves {c : Table n (Fin n)} (h : Laws c) (thin : ∀ i, Function.Injective (c i))
    (i : Fin n) : ∃ p : colorGroup c, p.val i=0 := by
  let first := Equiv.ofBijective (c 0) (Finite.injective_iff_bijective.mp (thin 0))
  let row := Equiv.ofBijective (c i) (Finite.injective_iff_bijective.mp (thin i))
  let p := row.trans first.symm
  have act (z : Fin n) : c 0 (p z)=c i z := first.apply_symm_apply _
  have pres (x y : Fin n) : c (p x) (p y)=c x y := by
    have q := h.pairs i x 0 (p x) (act x).symm
    obtain ⟨t,qt⟩ := List.mem_ofFn.mp (q.mem_iff.mp (List.mem_ofFn.mpr ⟨y,rfl⟩))
    obtain ⟨a,b⟩ := Prod.mk.inj qt
    exact (thin 0 (a.trans (act y).symm)) ▸ b
  exact ⟨⟨p,pres⟩,thin 0 ((act i).trans ((h.diagonal i i).mpr rfl))⟩

omit [NeZero n] in
theorem colorGroup_free {c : Table n (Fin n)} (thin : ∀ i, Function.Injective (c i))
    (p : colorGroup c) {x : Fin n} (fix : p.val x=x) : p=1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro y
  exact thin x (by simpa only [fix] using p.property x y)

theorem colorGroup_card {c : Table n (Fin n)} (h : Laws c) (thin : ∀ i, Function.Injective (c i)) :
    Nat.card (colorGroup c)=n := by
  let f := fun p : colorGroup c => p.val 0
  have inj : Function.Injective f := by
    intro p q eq
    apply Subtype.ext
    apply Equiv.ext
    intro y
    apply thin (p.val 0)
    change p.val 0=q.val 0 at eq
    exact (p.property 0 y).trans (by rw [eq]; exact (q.property 0 y).symm)
  have sur : Function.Surjective f := by
    intro x
    obtain ⟨p,hp⟩ := colorGroup_moves h thin x
    exact ⟨p⁻¹,p.val.symm_apply_eq.mpr hp.symm⟩
  simpa using Nat.card_congr (Equiv.ofBijective f ⟨inj,sur⟩)

abbrev Ten := Fin 10
private def shiftFn (k : Nat) (x : Ten) : Ten := ⟨x.val/5*5+(x.val+k)%5,by have:=x.isLt; omega⟩
def shift : Equiv.Perm Ten where
  toFun := shiftFn 1
  invFun := shiftFn 4
  left_inv := by native_decide
  right_inv := by native_decide

theorem ten_thin_rotation {c : Table 10 Ten} (h : Laws c) (thin : ∀ i, Function.Injective (c i)) :
    ∃ e : Equiv.Perm Ten, ∀ i j, c (e (shift i)) (e (shift j))=c (e i) (e j) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨u,order⟩ := exists_prime_orderOf_dvd_card' (G:=colorGroup c) 5 (by rw [colorGroup_card h thin]; decide)
  have five : orderOf u.val=5 := by simpa using order
  have nofix (x : Ten) : u.val x≠x := by
    intro hx
    have eq := colorGroup_free thin u hx
    simp [eq] at order
  have support : u.val.support=Finset.univ := Finset.ext fun x => by simp [Equiv.Perm.mem_support,nofix]
  obtain ⟨k,hk⟩ := Equiv.Perm.cycleType_prime_order (σ:=u.val) (by rw [five]; decide)
  have size := u.val.sum_cycleType
  rw [hk,support,five,Multiset.sum_replicate] at size
  simp at size
  have k1 : k=1 := by omega
  have shape : shift.cycleType=Multiset.replicate 2 5 := by native_decide
  have conj : IsConj shift u.val := Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [shape,hk,k1,five])
  obtain ⟨e,he⟩ := isConj_iff.mp conj
  have comm (x : Ten) : e (shift x)=u.val (e x) := by simpa using DFunLike.congr_fun he (e x)
  exact ⟨e,fun i j => by rw [comm,comm]; exact u.property (e i) (e j)⟩


def orbitBase (x : Ten) : Ten := if x.val<5 then 0 else 5
def back (x : Ten) : Equiv.Perm Ten := shift^(5-x.val%5)
def otherRow (a : Fin 5) (b z : Ten) : Ten :=
  (shift^(a.val*(z.val%5))) (if z.val<5 then b else 0)
def orbitTable (a : Fin 5) (b i j : Ten) : Ten :=
  if i.val<5 then back i j else otherRow a b (back i j)

private theorem orbitStart : ∀ z : Ten, (shift^(z.val%5)) (orbitBase z)=z := by native_decide
private theorem orbitBack : ∀ z : Ten, back z z=orbitBase z := by native_decide

theorem thin_ten_form {c : Table 10 Ten} (h : Laws c) (thin : ∀ i, Function.Injective (c i)) :
    ∃ (a : Fin 5) (b : Ten), Function.Injective (otherRow a b) ∧
      (∀ i j, orbitTable a b (otherRow a b i) (otherRow a b j)=orbitTable a b i j) ∧
      Iso (orbitTable a b) c := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨e,he⟩ := ten_thin_rotation h thin
  let label := Equiv.ofBijective (fun j => c (e 0) (e j))
    (Finite.injective_iff_bijective.mp ((thin (e 0)).comp e.injective))
  let d : Table 10 Ten := fun i j => label.symm (c (e i) (e j))
  have law : Laws d := h.transport e label.symm (fun _ _ _ _ eq => label.symm.injective eq)
  have zero (z : Ten) : d 0 z=z := label.symm_apply_apply z
  have dt (i : Ten) : Function.Injective (d i) := label.symm.injective.comp ((thin _).comp e.injective)
  let s : colorGroup d := ⟨shift,fun i j => congrArg label.symm (he i j)⟩
  obtain ⟨q,hq⟩ := colorGroup_moves law dt 5
  let H := Subgroup.zpowers s
  have os : orderOf s=5 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf shift=5
    exact orderOf_eq_prime (by native_decide) (by native_decide)
  have index := H.index_mul_card
  rw [colorGroup_card law dt,show Nat.card H=5 from (Nat.card_zpowers s).trans os] at index
  have norm := H.normal_of_index_eq_two (by omega)
  have inside := norm.conj_mem s (Subgroup.mem_zpowers s) q
  obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp inside)
  let a : Fin 5 := ⟨v,by simpa [os] using hv⟩
  let b := q.val 0
  have commute (x : Ten) : q.val (shift x)=(shift^a.val) (q.val x) := by
    have E := DFunLike.congr_fun (congrArg Subtype.val eq) (q.val x)
    simpa [s,a] using E.symm
  have iter (k : Nat) (x : Ten) : q.val ((shift^k) x)=(shift^(a.val*k)) (q.val x) := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ',Equiv.Perm.mul_apply,commute,ih,Nat.mul_succ,pow_add,Equiv.Perm.mul_apply,
                          ← Equiv.Perm.mul_apply,← pow_add,Nat.add_comm]
                   rw [pow_add,Equiv.Perm.mul_apply]
  have formula (x : Ten) : q.val x=otherRow a b x := by
    have step := iter (x.val%5) (orbitBase x)
    rw [orbitStart] at step
    by_cases z : x.val<5
    · simpa [orbitBase,otherRow,z,b] using step
    · simpa [orbitBase,otherRow,z,hq] using step
  have row (j : Ten) : d 5 j=q.val j := by simpa [hq,zero] using (q.property 5 j).symm
  have table (i j : Ten) : d i j=orbitTable a b i j := by
    have keep := (s^(5-i.val%5)).property i j
    change d (back i i) (back i j)=d i j at keep
    rw [orbitBack] at keep
    by_cases z : i.val<5
    · simpa [orbitBase,z,zero,orbitTable] using keep.symm
    · simpa [orbitBase,z,row,formula,orbitTable] using keep.symm
  refine ⟨a,b,?_,?_,e,?_⟩
  · exact fun x y eq => q.val.injective (by simpa only [formula] using eq)
  · intro i j
    simpa only [← table,← formula] using q.property i j
  · intro i j x y
    simp only [← table,d,label.symm.injective.eq_iff]

end QGI.RowCensus
