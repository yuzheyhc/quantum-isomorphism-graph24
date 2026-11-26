import RowBalance

namespace QGI.RowCensus

abbrev RowsAt := List (Nat × Nat)

theorem lookup_of_occurrence {β : Type} {xs : List (Nat × β)} {a : Nat} {b : β}
    (hit : ∃ v, (a,v)∈xs) (same : ∀ v, (a,v)∈xs → v=b) : xs.lookup a=some b := by
  induction xs with
  | nil => simp at hit
  | cons head tail ih =>
    obtain ⟨u,v⟩ := head
    by_cases eq : a=u
    · subst u; simp [List.lookup,same v List.mem_cons_self]
    · have no : (a==u)=false := beq_eq_false_iff_ne.mpr eq
      rw [List.lookup]; simp only [no]
      obtain ⟨w,hw⟩ := hit
      apply ih ⟨w,(List.mem_cons.mp hw).resolve_left (fun h => eq (congrArg Prod.fst h))⟩
      exact fun w hw => same w (List.mem_cons_of_mem _ hw)

theorem lookup_in {β : Type} {xs : List (Nat × β)} {a : Nat} {b : β}
    (hit : xs.lookup a=some b) : (a,b)∈xs := by
  induction xs with
  | nil => simp at hit
  | cons head tail ih =>
    obtain ⟨u,v⟩ := head
    by_cases eq : a=u
    · subst u; simp [List.lookup] at hit; subst v; exact List.mem_cons_self
    · have no : (a==u)=false := beq_eq_false_iff_ne.mpr eq
      exact List.mem_cons_of_mem _ (ih (by simpa [List.lookup,no] using hit))

def wordDigits (n w : Nat) := List.ofFn (fun z : Fin n => digit n w z.val)
def labelPairs (n u v : Nat) := List.ofFn fun j : Fin n => (digit n u j.val,digit n v j.val)
def recolorRow (n u v r : Nat) :=
  let labels := labelPairs n u v
  encode n ((wordDigits n r).map fun a => (labels.lookup a).getD 0)

def indexed (n : Nat) (rs : List Nat) : RowsAt :=
  (List.range rs.length).map fun i => (i,encode n (wordDigits n (rs.getD i 0)))

def links (n : Nat) (old : RowsAt) (first : List Nat) : List Tag :=
  old.flatMap fun i => old.filterMap fun j =>
    let a := digit n i.2 j.1
    if first.count a=1 then some (a,i.2,j.2) else none

/-- A relation of valency one determines the whole row at its other endpoint. -/
def predict (n : Nat) (rs : List Nat) : RowsAt :=
  let old := indexed n rs
  let moves := links n old (wordDigits n (rs.getD 0 0))
  (old ++ old.flatMap (fun o => (List.range n).filterMap fun z =>
    (moves.lookup (digit n o.2 z)).map (fun p => (z,recolorRow n p.1 p.2 o.2)))).dedup

def Describes {n : Nat} (m : Matrix n) (old : RowsAt) :=
  ∀ t∈old, ∃ i : Fin n, t=(i.val,word m i)

private theorem index_sound {n : Nat} {m : Matrix n} {rs : List Nat} (f : Fits m rs) (length : rs.length≤n) :
    Describes m (indexed n rs) := by
  intro t ht
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
  have bound := List.mem_range.mp hj
  let i : Fin n := ⟨j,lt_of_lt_of_le bound length⟩
  refine ⟨i,Prod.ext rfl (congrArg (encode n) ?_)⟩
  exact congrArg List.ofFn (funext (fun x => f i x bound))

theorem rename_one {n : Nat} [NeZero n] {m : Matrix n} (h : Laws m)
    (i j x y u v : Fin n) (thin : thinEdge m i j) (eq : m i j=m x y) (arg : m i u=m x v) :
    m j u=m y v := by
  have localEq (a b : Fin n) (ab : m i a=m i b) : m j a=m j b := by
    obtain ⟨t,ht⟩ := List.mem_ofFn.mp ((h.pairs _ _ _ _ ab).mem_iff.mp (List.mem_ofFn.mpr ⟨j,rfl⟩))
    obtain ⟨e1,e2⟩ := Prod.mk.inj ht
    rw [thin t e1] at e2
    exact (h.reverse _ _ _ _ e2).symm
  obtain ⟨t,ht⟩ := List.mem_ofFn.mp ((h.pairs _ _ _ _ eq).mem_iff.mpr (List.mem_ofFn.mpr ⟨v,rfl⟩))
  obtain ⟨e1,e2⟩ := Prod.mk.inj ht
  exact (localEq u t (arg.trans e1.symm)).trans e2

theorem thin_degree {n : Nat} [NeZero n] {m : Matrix n} (h : Laws m)
    (i j : Fin n) (one : degree m (m i j)=1) : thinEdge m i j := by
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp ((fiber_card h i _).trans one)
  have e (w : Fin n) (hw : m i w=m i j) : w=z := Finset.mem_singleton.mp
    (hz ▸ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩))
  exact fun w hw => (e w hw).trans (e j rfl).symm

theorem predict_sound {n : Nat} [NeZero n] (m : Matrix n) (h : Laws m) (rs : List Nat)
    (f : Fits m rs) (positive : 0<rs.length) (length : rs.length≤n) : Describes m (predict n rs) := by
  let first := wordDigits n (rs.getD 0 0)
  have old := index_sound f length
  have deg (a : Fin n) : first.count a.val=degree m a := by
    have val (z : Fin n) : digit n (rs.getD 0 0) z.val=(m 0 z).val := f 0 z positive
    simp only [first,wordDigits,val,countFiber,degree,fiber,Fin.val_inj]
  intro t ht
  rcases List.mem_append.mp (List.mem_dedup.mp ht) with original|guessed
  · exact old _ original
  obtain ⟨o,ho,hp⟩ := List.mem_flatMap.mp guessed
  obtain ⟨z,hz,mapped⟩ := List.mem_filterMap.mp hp
  obtain ⟨⟨u,v⟩,lookup,rfl⟩ := Option.map_eq_some_iff.mp mapped
  obtain ⟨x,rfl⟩ := old _ ho
  let y : Fin n := ⟨z,List.mem_range.mp hz⟩
  have lm := lookup_in lookup
  obtain ⟨a,ha,more⟩ := List.mem_flatMap.mp lm
  obtain ⟨b,hb,edge⟩ := List.mem_filterMap.mp more
  obtain ⟨i,rfl⟩ := old _ ha
  obtain ⟨j,rfl⟩ := old _ hb
  change (if first.count (digit n (word m i) j.val)=1 then some (_,word m i,word m j) else none)=_ at edge
  split at edge
  next e =>
    have e' : degree m (m i j)=1 := by simpa only [digit_word,deg] using e
    have ed := Option.some.inj edge
    obtain ⟨between,words⟩ := Prod.mk.inj ed
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj words
    have eq : m i j=m x y := Fin.ext (by simpa only [digit_word] using (show digit n (word m i) j.val=digit n (word m x) y.val from between))
    refine ⟨y,Prod.ext rfl (congrArg (encode n) ?_)⟩
    simp only [List.map_ofFn,wordDigits,recolorRow,Function.comp_def]
    apply congrArg List.ofFn
    funext s
    simp only [digit_word]
    have appears := (h.row_perm i).mem_iff.mpr ((h.row_perm x).mem_iff.mp (List.mem_ofFn.mpr ⟨s,rfl⟩))
    obtain ⟨a,ea⟩ := List.mem_ofFn.mp appears
    have l := lookup_of_occurrence (xs:=labelPairs n (word m i) (word m j)) (a:=(m x s).val)
      (b:=(m y s).val) (by exact ⟨(m j a).val,List.mem_ofFn.mpr ⟨a,by simp [ea]⟩⟩) (by
      intro v hv
      obtain ⟨z,hz⟩ := List.mem_ofFn.mp hv
      simp only [digit_word,Prod.mk.injEq] at hz
      exact hz.2.symm.trans (congrArg Fin.val (rename_one h i j x y z s (thin_degree h _ _ e') eq (Fin.ext hz.1))))
    simp [l]
  next => simp at edge

end QGI.RowCensus
