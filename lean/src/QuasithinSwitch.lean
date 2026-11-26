import UnitRowExtensions

namespace QGI.RowCensus

variable {n : Nat} [NeZero n] {m : Table n (Fin n)}

private theorem sameBlockHit (h : Laws m) (o i i' j : Fin n) (eq : m o i=m o i') :
    ∃ z, m o z=m o j ∧ m i' z=m i j := by
  obtain ⟨z,hz⟩ := List.mem_ofFn.mp ((h.pairs o i o i' eq).mem_iff.mp (List.mem_ofFn.mpr ⟨j,rfl⟩))
  exact ⟨z,Prod.mk.inj hz⟩

/-- In the partition given by the colors out of a basepoint, simultaneously
swapping the members of every two-point class preserves every color. -/
theorem quasithin_switch (h : Laws m) (o : Fin n) (s : Fin n → Fin n)
    (stays : ∀ x, m o (s x)=m o x)
    (covers : ∀ x z, m o z=m o x → z=x ∨ z=s x) :
    ∀ i j, m (s i) (s j)=m i j := by
  intro i j
  by_contra different
  obtain ⟨u,hu,cu⟩ := sameBlockHit h o j (s j) i (stays j).symm
  have b : m i (s j)=m i j := by
    rcases covers i u hu with rfl|rfl
    · exact h.reverse _ _ _ _ cu
    · exact (different (h.reverse _ _ _ _ cu)).elim
  obtain ⟨v,hv,cv⟩ := sameBlockHit h o (s i) i (s j) (stays i)
  rcases covers j v (hv.trans (stays j)) with rfl|rfl
  · exact different cv.symm
  · exact different (cv.symm.trans b)

/-- Decode a point switch from one row. Its two required properties are
checked directly, so the pruning rule also works on mixed-valency input. -/
def switchAt (w : Nat) (i : Fin n) := ((List.finRange n).find? fun j =>
  j != i && digit n w j.val==digit n w i.val).getD i

def switchOK (n : Nat) (w : Nat) : Bool :=
  let s := switchAt (n:=n) w
  decide ((∀ i : Fin n, digit n w (s i).val=digit n w i.val) ∧
    (∀ i j : Fin n, digit n w j.val=digit n w i.val → j=i ∨ j=s i) ∧ ∀ i, s (s i)=i)

def transfer (n r w : Nat) := encode n (List.ofFn fun j : Fin n => digit n r (switchAt w j).val)

def addSwitch (n : Nat) [NeZero n] (source item : Nat × Nat) : Nat × Nat :=
  ((switchAt source.2 (Fin.ofNat' n item.1)).val,transfer n item.2 source.2)

theorem addSwitch_sound (h : Laws m) {o i : Fin n} (ok : switchOK n (word m o)=true) :
    ∃ j : Fin n, addSwitch n (o.val,word m o) (i.val,word m i)=(j.val,word m j) := by
  let s := switchAt (n:=n) (word m o)
  obtain ⟨stays,covers,invol⟩ := of_decide_eq_true ok
  have col := quasithin_switch h o s (fun x => Fin.ext (by simpa only [digit_word] using stays x))
    (fun x z eq => covers x z (by simpa only [digit_word] using congrArg Fin.val eq))
  refine ⟨s i,Prod.ext (by simp [addSwitch,s,Fin.ofNat',Nat.mod_eq_of_lt i.isLt]) ?_⟩
  apply congrArg (encode n)
  apply congrArg List.ofFn
  funext j
  have same := col i (s j)
  rw [show s (s j)=j from invol j] at same
  simpa only [digit_word] using congrArg Fin.val same.symm

def addRound (n : Nat) [NeZero n] (old : RowsAt) : RowsAt :=
  (old ++ old.flatMap fun o => if switchOK n o.2 then old.map (addSwitch n o) else []).dedup

private theorem round_sound (h : Laws m) (old : RowsAt) (d : Describes m old) :
    Describes m (addRound n old) := by
  intro t ht
  rcases List.mem_append.mp (List.mem_dedup.mp ht) with prev|next
  · exact d _ prev
  obtain ⟨o,ho,u⟩ := List.mem_flatMap.mp next
  obtain ⟨i,rfl⟩ := d _ ho
  split at u
  next ok =>
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp u
    obtain ⟨j,rfl⟩ := d _ hv
    exact addSwitch_sound h ok
  next => simp at u

/-- Disagreement about the row attached to one vertex rules out a prefix. -/
def uniqueRows (rows : RowsAt) := rows.all fun p => rows.lookup p.1 == some p.2

omit [NeZero n] in
theorem describes_unique {rows : RowsAt} (d : Describes m rows) : uniqueRows rows=true := by
  apply List.all_eq_true.mpr
  intro p hp
  obtain ⟨i,e⟩ := d _ hp
  subst p
  apply beq_iff_eq.mpr
  apply lookup_of_occurrence ⟨_,hp⟩
  intro v hv
  obtain ⟨j,eq⟩ := d _ hv
  obtain ⟨h1,h2⟩ := Prod.mk.inj eq
  exact h2.trans (congrArg (word m) (Fin.ext h1.symm))

def switchedRows (n : Nat) [NeZero n] : Nat → RowsAt → RowsAt
  | 0, old => old
  | f+1, old =>
    let next := addRound n old
    if next.length=old.length || !uniqueRows next then next else switchedRows n f next

theorem switched_sound (h : Laws m) (fuel : Nat) (old : RowsAt) (d : Describes m old) :
    Describes m (switchedRows n fuel old) := by
  induction fuel generalizing old with
  | zero => exact d
  | succ fuel ih =>
    simp only [switchedRows]
    split
    · exact round_sound h _ d
    · exact ih _ (round_sound h _ d)

private def rowTags (n : Nat) (rows : RowsAt) : List Tag :=
  rows.flatMap fun u => rows.map fun v =>
    (digit n u.2 v.1,digit n v.2 u.1,signature n u.2 v.2)

private def allTagsOK (n : Nat) (rows : RowsAt) :=
  let tags := rowTags n rows
  tags.all fun t => tags.lookup t.1 == some t.2

open private tagOf RealTag weight sumFn lookup_consistent from RowCensusSound in
theorem describes_tags {rows : RowsAt} (h : Laws m) (d : Describes m rows) : allTagsOK n rows=true := by
  have good : ∀ t∈rowTags n rows, RealTag m t := by
    intro t ht
    obtain ⟨u,hu,within⟩ := List.mem_flatMap.mp ht
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp within
    obtain ⟨i,rfl⟩ := d _ hu
    obtain ⟨j,rfl⟩ := d _ hv
    refine ⟨i,j,?_⟩
    simp only [digit_word,tagOf,signature,weight,sumFn]
  apply List.all_eq_true.mpr
  intro t ht
  exact beq_iff_eq.mpr (lookup_consistent h good ht)

def spreadSwitches (n : Nat) [NeZero n] (rs : List Nat) := switchedRows n n (indexed n rs)

open private index_sound from RowPredictions in
theorem spread_sound (h : Laws m) {rs : List Nat} (f : Fits m rs) (len : rs.length≤n) :
    Describes m (spreadSwitches n rs) := switched_sound h _ _ (index_sound f len)

def validSwitches (n : Nat) [NeZero n] (rs : List Nat) :=
  let rows := spreadSwitches n rs
  uniqueRows rows && allTagsOK n rows

theorem validSwitches_sound (h : Laws m) {rs : List Nat} (f : Fits m rs) (len : rs.length≤n) :
    validSwitches n rs=true :=
  Bool.and_eq_true_iff.mpr ⟨describes_unique (spread_sound h f len),describes_tags h (spread_sound h f len)⟩

/-- Once the switches determine the next row, it needs no search. -/
def switchRows (n : Nat) [NeZero n] (rs : List Nat) :=
  let known := spreadSwitches n rs
  if !uniqueRows known || !allTagsOK n known then [] else
    match known.lookup rs.length with
    | some w => [w]
    | none => (unitRows n rs).filter fun w => validSwitches n (rs++[w])

open private extend from RowCensusSound in
theorem switch_complete (m : Matrix n) (h : Laws m) (rs : List Nat) (f : Fits m rs)
    (positive : 0<rs.length) (k : Fin n) (hk : k.val=rs.length) : word m k∈switchRows n rs := by
  have bound : rs.length<n := hk ▸ k.isLt
  have d := spread_sound h f bound.le
  simp only [switchRows,describes_unique d,describes_tags h d,Bool.not_true,Bool.false_or,Bool.false_eq_true,if_false]
  cases e : (spreadSwitches n rs).lookup rs.length with
  | some w =>
    obtain ⟨i,hit⟩ := d _ (lookup_in e)
    obtain ⟨index,rfl⟩ := Prod.mk.inj hit
    simpa only [show i=k from Fin.ext (index.symm.trans hk.symm),List.mem_singleton]
  | none =>
    exact List.mem_filter.mpr ⟨unit_complete m h rs f positive k hk,
      validSwitches_sound h (extend f k hk) (by simp; omega)⟩

end QGI.RowCensus
