import RowSwitchKernelSound

namespace QGI.RowCensus
open private allTagsOK from QuasithinSwitch

variable {n : Nat} [NeZero n] {m : Matrix n}

private def saved (n : Nat) (xs : RowsAt) : List Tag :=
  xs.flatMap fun i => xs.map fun j => (digit n i.2 j.1,i.2,j.2)

private theorem saved_entry {xs : RowsAt} (d : Describes m xs) {a u v : Nat}
    (l : (saved n xs).lookup a=some (u,v)) :
    ∃ i j : Fin n, (m i j).val=a ∧ word m i=u ∧ word m j=v := by
  obtain ⟨o,ho,rest⟩ := List.mem_flatMap.mp (lookup_mem l)
  obtain ⟨p,hp,eq⟩ := List.mem_map.mp rest
  obtain ⟨i,rfl⟩ := d _ ho
  obtain ⟨j,rfl⟩ := d _ hp
  exact ⟨i,j,by simpa only [digit_word,Prod.mk.injEq] using eq⟩

/-- Admissible colors for a particular entry. Known row-pair supports and
transpose valencies can be checked before generating the rest of the row. -/
private def domainQ (n : Nat) (known : RowsAt) (tags : List Tag) (first : List Nat)
    (k j a : Nat) : Bool :=
  (decide (j=k) == decide (a=first.getD 0 0)) &&
  known.all fun i =>
    let c := digit n i.2 k
    (i.1 != j || first.count c==first.count a) &&
    match tags.lookup c with
    | none => true
    | some (u,v) => (List.range n).any fun z =>
      digit n u z == digit n i.2 j && digit n v z == a

private theorem domainQ_sound (h : Laws m) {xs : RowsAt} (d : Describes m xs) (k j : Fin n) :
    domainQ n xs (saved n xs) (wordDigits n (word m 0)) k.val j.val (m k j).val=true := by
  have diag : j.val=k.val ↔ (m k j).val=(m 0 0).val := by
    simp only [Fin.val_inj,h.diagonal,eq_comm (a:=j)]
  have get0 : (wordDigits n (word m 0)).getD 0 0=(m 0 0).val := by
    simp [wordDigits,List.getD_eq_getElem?_getD,Nat.pos_of_ne_zero (NeZero.ne n)]
  have cnt (a : Fin n) : (wordDigits n (word m 0)).count a.val=degree m a := by
    simp only [wordDigits,digit_word,countFiber,Fin.val_inj,degree,fiber]
  simp only [domainQ,get0,propext diag,beq_self_eq_true,Bool.true_and]
  apply List.all_eq_true.mpr
  intro p hp
  obtain ⟨i,rfl⟩ := d _ hp
  apply Bool.and_eq_true_iff.mpr
  constructor
  · by_cases eq : i=j
    · subst i; simp [digit_word,cnt,degree_reverse h j k]
    · simp [Fin.val_ne_of_ne eq]
  · cases e : (saved n xs).lookup (digit n (word m i) k.val) with
    | none => rfl
    | some pair =>
      obtain ⟨u,v⟩ := pair
      obtain ⟨s,t,st,rfl,rfl⟩ := saved_entry d e
      have link : m s t=m i k := Fin.ext (by simpa only [digit_word] using st)
      obtain ⟨z,eq⟩ := List.mem_ofFn.mp ((h.pairs i k s t link.symm).mem_iff.mp (List.mem_ofFn.mpr ⟨j,rfl⟩))
      obtain ⟨e1,e2⟩ := Prod.mk.inj eq
      exact List.any_eq_true.mpr ⟨z.val,List.mem_range.mpr z.isLt,by simp [e1,e2]⟩

/-- A thin link, or an automorphism fixing the row origin, forces equal entries. -/
private def tied (n : Nat) [NeZero n] (xs : RowsAt) (first : List Nat) (k i j : Fin n) :=
  (match xs.lookup i.val, xs.lookup j.val with
  | some u, some v => digit n u k.val == digit n v k.val
  | _,_ => false) || xs.any fun o =>
    (first.count (digit n o.2 k.val)==1 && digit n o.2 i.val==digit n o.2 j.val) ||
    (switchOK n o.2 && decide (switchAt o.2 k=k ∧ switchAt o.2 i=j))

private theorem tied_sound (h : Laws m) {xs : RowsAt} (d : Describes m xs) {k i j : Fin n}
    (hit : tied n xs (wordDigits n (word m 0)) k i j=true) : m k i=m k j := by
  rcases Bool.or_eq_true_iff.mp hit with trans|hit
  · cases u : xs.lookup i.val <;> cases v : xs.lookup j.val <;> simp [u,v] at trans
    obtain ⟨x,ex⟩ := d _ (lookup_in u)
    obtain ⟨y,ey⟩ := d _ (lookup_in v)
    obtain ⟨hx,rfl⟩ := Prod.mk.inj ex
    obtain ⟨hy,rfl⟩ := Prod.mk.inj ey
    rw [show x=i from Fin.ext hx.symm,show y=j from Fin.ext hy.symm] at trans
    exact h.reverse _ _ _ _ (Fin.ext (by simpa using trans))
  obtain ⟨o,ho,eq⟩ := List.any_eq_true.mp hit
  obtain ⟨s,rfl⟩ := d _ ho
  rcases Bool.or_eq_true_iff.mp eq with thin|flip
  · have ⟨one,same⟩ := Bool.and_eq_true_iff.mp thin
    have val : degree m (m s k)=1 := by
      simpa only [wordDigits,digit_word,countFiber,Fin.val_inj,degree,fiber,beq_iff_eq] using one
    exact rename_one h s k s k i j (thin_degree h s k val) rfl (Fin.ext (by simpa using same))
  · have ⟨ok,p⟩ := Bool.and_eq_true_iff.mp flip
    obtain ⟨stay,cov,_⟩ := of_decide_eq_true ok
    obtain ⟨fixed,moved⟩ := of_decide_eq_true p
    have keep := quasithin_switch h s (switchAt (word m s))
      (fun x => Fin.ext (by simpa only [digit_word] using stay x))
      (fun x z e => cov x z (by simpa only [digit_word] using congrArg Fin.val e)) k i
    rw [fixed,moved] at keep
    exact keep.symm

private def fillTied : List (List Nat × Option Nat) → List Nat → List Nat → List (List Nat)
  | [], _, _ => [[]]
  | (opts,link)::tail, left, past =>
    let vals := match link with
      | some j => [past.getD j 0].filter (·∈opts)
      | none => opts
    (vals.filter (·∈left)).flatMap fun a => (fillTied tail (left.erase a) (past++[a])).map (a :: ·)

private theorem fillTied_mem {v left past : List Nat} {opts : List (List Nat × Option Nat)}
    (perm : v.Perm left) (allow : List.Forall₂ (fun o a => a∈o.1) opts v)
    (same : ∀ i (hi : i<opts.length) j, opts[i].2=some j → (past++v).getD j 0=v.getD i 0)
    (early : ∀ i (hi : i<opts.length) j, opts[i].2=some j → j<past.length+i) :
    v∈fillTied opts left past := by
  induction allow generalizing left past with
  | nil => simp [fillTied]
  | @cons o a os vals ha more ih =>
    have mem : a∈left := perm.mem_iff.mp List.mem_cons_self
    have head (j) (link : o.2=some j) : past.getD j 0=a := by
      have lt := early 0 (by simp) j link
      have he := same 0 (by simp) j link
      have hj : j<past.length := by simpa using lt
      rw [List.getD_append _ _ _ _ hj] at he
      exact he
    apply List.mem_flatMap.mpr
    refine ⟨a,List.mem_filter.mpr ⟨?_,by simpa using mem⟩,List.mem_map.mpr ⟨vals,?_,rfl⟩⟩
    · cases e : o.2 with
      | none => exact ha
      | some j => exact List.mem_filter.mpr ⟨List.mem_singleton.mpr (head j e).symm,by simpa using ha⟩
    · apply ih (left:=left.erase a) (past:=past++[a]) (by simpa using perm.erase a)
      · intro i hi j eq
        have he := same (i+1) (by simp; omega) j eq
        simpa [List.append_assoc] using he
      · intro i hi j eq
        have he := early (i+1) (by simp; omega) j eq
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he

private def specs (n : Nat) [NeZero n] (known : RowsAt) (first : List Nat) (k : Fin n) :=
  let tags := saved n known
  List.ofFn fun j : Fin n =>
    let opt := first.dedup.filter (domainQ n known tags first k.val j.val)
    let idx := ((List.finRange n).find? fun i => decide (i.val<j.val) && tied n known first k i j).map Fin.val
    (opt,idx)

private def eligible (n : Nat) [NeZero n] (known : RowsAt) (first : List Nat) (k : Fin n) :=
  (fillTied (specs n known first k) first []).map (encode n)

private theorem eligible_sound (h : Laws m) (k : Fin n) {xs : RowsAt} (d : Describes m xs) :
    word m k∈eligible n xs (wordDigits n (word m 0)) k := by
  let base := wordDigits n (word m 0)
  let opts := specs n xs base k
  let actual := List.ofFn fun j => (m k j).val
  have perm : actual.Perm base := by
    simpa only [actual,base,wordDigits,digit_word,List.map_ofFn,Function.comp_def] using (h.row_perm k).map Fin.val
  have detail (i : Nat) (hi : i<opts.length) (j : Nat) (eq : opts[i].2=some j) :
      ∃ ix jy : Fin n, ix.val=i ∧ jy.val=j ∧ j < i ∧ m k jy=m k ix := by
    have inBound : i<n := by simpa [opts,specs] using hi
    let ix : Fin n := ⟨i,inBound⟩
    change ((specs n xs base k)[i]).2=some j at eq
    simp only [specs,List.getElem_ofFn,Option.map_eq_some_iff] at eq
    obtain ⟨jy,found,rfl⟩ := eq
    have test := List.find?_some found
    obtain ⟨lt,link⟩ := Bool.and_eq_true_iff.mp test
    exact ⟨ix,jy,rfl,rfl,of_decide_eq_true lt,tied_sound h d link⟩
  apply List.mem_map.mpr
  refine ⟨actual,fillTied_mem perm ?_ ?_ ?_,rfl⟩
  · apply forall₂_ofFn
    intro j
    exact List.mem_filter.mpr ⟨List.mem_dedup.mpr (perm.mem_iff.mp (List.mem_ofFn.mpr ⟨j,rfl⟩)),domainQ_sound h d k j⟩
  · intro i hi j eq
    obtain ⟨ix,jy,rfl,rfl,_,color⟩ := detail i hi j eq
    simp [actual,List.getD_eq_getElem?_getD,color]
  · intro i hi j eq
    obtain ⟨_,_,_,_,lt,_⟩ := detail i hi j eq
    simpa using lt

/-- Extend the prefix only by rows satisfying the constraints from the
already determined switches, then certify consistency of their closure. -/
def fastSwitchRows (n : Nat) [NeZero n] (rs : List Nat) :=
  let known := spreadSwitches n rs
  if !uniqueRows known || !allTagsOK n known then [] else
    match known.lookup rs.length with
    | some w => [w]
    | none => (eligible n known (wordDigits n (rs.getD 0 0)) (Fin.ofNat' n rs.length)).filter
        fun w => RowSwitchKernel.accepts n (rs++[w]) && validSwitches n (rs++[w])

open private extend from RowCensusSound in
theorem fastSwitch_complete (m : Matrix n) (h : Laws m) (rs : List Nat) (f : Fits m rs)
    (positive : 0<rs.length) (k : Fin n) (hk : k.val=rs.length) : word m k∈fastSwitchRows n rs := by
  have bound : rs.length<n := hk ▸ k.isLt
  have d := spread_sound h f bound.le
  simp only [fastSwitchRows,describes_unique d,describes_tags h d,Bool.not_true,Bool.false_or,Bool.false_eq_true,if_false]
  cases e : (spreadSwitches n rs).lookup rs.length with
  | some w =>
    obtain ⟨i,hit⟩ := d _ (lookup_in e)
    obtain ⟨index,rfl⟩ := Prod.mk.inj hit
    simpa only [show i=k from Fin.ext (index.symm.trans hk.symm),List.mem_singleton]
  | none =>
    have base : wordDigits n (rs.getD 0 0)=wordDigits n (word m 0) :=
      congrArg List.ofFn (funext (fun j => (f 0 j positive).trans (digit_word m 0 j).symm))
    have index : Fin.ofNat' n rs.length=k := Fin.ext (by simp [Fin.ofNat',Nat.mod_eq_of_lt bound,hk])
    exact List.mem_filter.mpr ⟨by rw [base,index]; exact eligible_sound h k d,
      Bool.and_eq_true_iff.mpr ⟨RowSwitchKernel.accepts_sound h (extend f k hk) (by simp; omega),
        validSwitches_sound h (extend f k hk) (by simp; omega)⟩⟩

end QGI.RowCensus
