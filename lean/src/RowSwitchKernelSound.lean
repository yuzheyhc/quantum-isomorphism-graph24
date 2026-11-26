import RowSwitchKernel
import QuasithinSwitch

namespace QGI.RowSwitchKernel

open RowCensus
variable {n : Nat} [NeZero n] {m : Matrix n}

def dense (m : Matrix n) (i : Fin n) : Row := (List.ofFn fun j => (m i j).val).toArray

@[simp] theorem value_dense (i j : Fin n) : value (dense m i) j.val=(m i j).val := by simp [value,dense]

private theorem tabulate (g : Nat → Nat) (f : Fin n → Nat) (eq : ∀ j : Fin n, g j.val=f j) :
    ((List.range n).map g).toArray=(List.ofFn f).toArray := by
  apply congrArg List.toArray
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simpa using eq ⟨i,by simpa using hi⟩

def Good (m : Matrix n) (xs : Known) := ∀ p∈xs, ∃ i : Fin n, p=(i.val,dense m i)

private theorem start_good {rs : List Nat} (fits : Fits m rs) (len : rs.length≤n) : Good m (start n rs) := by
  intro p hp
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  have hi := List.mem_range.mp hi
  let x : Fin n := ⟨i,lt_of_lt_of_le hi len⟩
  exact ⟨x,Prod.ext rfl (tabulate _ _ (fun z => fits x z hi))⟩

private def Symmetry (m : Matrix n) (p : Row) :=
  ∃ f : Fin n → Fin n, (∀ i, value p i.val=(f i).val) ∧
    (∀ i, f (f i)=i) ∧ ∀ i j, m (f i) (f j)=m i j

private theorem prepared (h : Laws m) {old : Known} (d : Good m old) {p : Row} (hp : p∈taggedMaps n old) :
    Symmetry m p := by
  obtain ⟨v,hv,eq⟩ := List.mem_filterMap.mp hp
  obtain ⟨o,rfl⟩ := d _ hv
  dsimp only at eq
  split at eq
  next ok =>
    obtain rfl := Option.some.inj eq
    let p := swapMap n (dense m o)
    have test (i : Fin n) := List.all_eq_true.mp ok i.val (List.mem_range.mpr i.isLt)
    have unpacked (i : Fin n) : value p i.val<n ∧ value (dense m o) (value p i.val)=value (dense m o) i.val ∧
        value p (value p i.val)=i.val ∧ ∀ j : Fin n, value (dense m o) j.val=value (dense m o) i.val →
        j.val=value p i.val ∨ j.val=i.val := by
      have t := test i
      simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true] at t
      refine ⟨t.1.1.1,t.1.1.2,t.1.2,?_⟩
      intro j e
      have s := t.2 j.val (List.mem_range.mpr j.isLt)
      simpa only [e,bne_self_eq_false,Bool.false_or,Bool.or_eq_true,beq_iff_eq] using s
    let f (i : Fin n) : Fin n := ⟨value p i.val,(unpacked i).1⟩
    refine ⟨f,fun _ => rfl,fun i => Fin.ext (unpacked i).2.2.1,?_⟩
    apply quasithin_switch h o f
    · intro i
      apply Fin.ext
      simpa only [←value_dense (m:=m) o (f i),←value_dense (m:=m) o i] using (unpacked i).2.1
    · intro i j e
      rcases (unpacked i).2.2.2 j (by simpa using congrArg Fin.val e) with hit|hit
      · exact Or.inr (Fin.ext hit)
      · exact Or.inl (Fin.ext hit)
  next => cases eq

private theorem add_good {p : Row} (symm : Symmetry m p) {v : Placed} (hv : ∃ i : Fin n, v=(i.val,dense m i))
    {xs : Known} (d : Good m xs) : ∃ ys, add n p v xs=some ys ∧ Good m ys := by
  obtain ⟨f,coord,invol,keep⟩ := symm
  obtain ⟨i,rfl⟩ := hv
  have moved : act n p (dense m i)=dense m (f i) := tabulate _ _ (fun j => by
    simp only [coord,value_dense]
    have e := keep i (f j)
    rw [invol] at e
    exact congrArg Fin.val e.symm)
  simp only [add,coord,moved]
  cases l : xs.lookup (f i).val with
  | none => exact ⟨_,rfl,fun v mem => (List.mem_cons.mp mem).elim (fun e => ⟨f i,e⟩) (d v)⟩
  | some r =>
    obtain ⟨j,eq⟩ := d _ (lookup_in l)
    obtain ⟨hj,rfl⟩ := Prod.mk.inj eq
    have same : j=f i := Fin.ext hj.symm
    exact ⟨xs,by simp [same],d⟩

private theorem map_good {p : Row} (symm : Symmetry m p) (items : Known) (g : Good m items)
    (xs : Known) (d : Good m xs) : ∃ ys, applyMap n p items xs=some ys ∧ Good m ys := by
  induction items generalizing xs with
  | nil => exact ⟨xs,rfl,d⟩
  | cons v rest ih =>
    obtain ⟨ys,add,dy⟩ := add_good symm (g _ List.mem_cons_self) d
    obtain ⟨zs,fin,dz⟩ := ih (fun w hw => g _ (List.mem_cons_of_mem _ hw)) ys dy
    exact ⟨zs,by simp [applyMap,add,fin],dz⟩

private theorem all_good (old : Known) (g : Good m old) (ps : List Row) (ok : ∀ p∈ps, Symmetry m p)
    (xs : Known) (d : Good m xs) : ∃ ys, applyAll n old ps xs=some ys ∧ Good m ys := by
  induction ps generalizing xs with
  | nil => exact ⟨xs,rfl,d⟩
  | cons p rest ih =>
    obtain ⟨ys,step,dy⟩ := map_good (ok _ List.mem_cons_self) old g xs d
    obtain ⟨zs,fin,dz⟩ := ih (fun q hq => ok _ (List.mem_cons_of_mem _ hq)) ys dy
    exact ⟨zs,by simp [applyAll,step,fin],dz⟩

private theorem coherent_good (h : Laws m) {old : Known} (g : Good m old) : coherent n old=true := by
  let tag (i j : Fin n) := ((m i j).val,(m j i).val,sig n (dense m i) (dense m j))
  let tags := old.flatMap fun i => old.map fun j => (value i.2 j.1,value j.2 i.1,sig n i.2 j.2)
  have real (t) (ht : t∈tags) : ∃ i j, t=tag i j := by
    obtain ⟨a,ha,tail⟩ := List.mem_flatMap.mp ht
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp tail
    obtain ⟨i,rfl⟩ := g _ ha
    obtain ⟨j,rfl⟩ := g _ hb
    exact ⟨i,j,by simp [tag]⟩
  have total (i j : Fin n) : sig n (dense m i) (dense m j)=
      (List.ofFn fun z => weight (m i z).val (m j z).val).sum := by
    exact congrArg List.sum (List.toArray_inj (tabulate _ _ (fun z => by simp)))
  apply List.all_eq_true.mpr
  intro t ht
  apply beq_iff_eq.mpr
  apply lookup_of_occurrence ⟨t.2,ht⟩
  intro v hv
  obtain ⟨i,j,rfl⟩ := real t ht
  obtain ⟨x,y,eq⟩ := real _ hv
  have ⟨same,tail⟩ := Prod.mk.inj eq
  have col : m i j=m x y := Fin.ext same
  rw [tail]
  apply Prod.ext (congrArg Fin.val (h.reverse _ _ _ _ col).symm)
  have s := ((h.pairs _ _ _ _ col).map (fun z => weight z.1.val z.2.val)).sum_eq
  simpa only [tag,total,List.map_ofFn,Function.comp_def] using s.symm

private theorem run_good (h : Laws m) (f : Nat) (xs : Known) (d : Good m xs) : run n f xs=true := by
  induction f generalizing xs with
  | zero => exact coherent_good h d
  | succ fuel ih =>
    obtain ⟨ys,step,dy⟩ := all_good xs d _ (fun _ hp => prepared h d hp) xs d
    simp only [run,step]
    split
    · exact coherent_good h dy
    · exact ih ys dy

theorem accepts_sound (h : Laws m) {rs : List Nat} (f : Fits m rs) (len : rs.length≤n) :
    accepts n rs=true := run_good h _ _ (start_good f len)

end QGI.RowSwitchKernel
