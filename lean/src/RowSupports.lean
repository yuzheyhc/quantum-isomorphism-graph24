import RowCensusSound

namespace QGI.RowCensus

private def heads (n : Nat) (rs : List Nat) : List Tag :=
  (List.range rs.length).flatMap fun i => (List.range rs.length).map fun j =>
    (entry n rs i j,rs.getD i 0,rs.getD j 0)

private def domain (n : Nat) (rs : List Nat) (known : List Tag) (j x : Nat) : Bool :=
  (List.range rs.length).all fun i => match known.lookup (entry n rs i rs.length) with
    | none => true
    | some (u,v) => (List.range n).any fun z => digit n u z == entry n rs i j && digit n v z == x

private def fill : List (List Nat) → List Nat → List (List Nat)
  | [],_ => [[]]
  | opts::tail,left => (opts.filter (·∈left)).flatMap fun x => (fill tail (left.erase x)).map (x :: ·)

def supportedRows (n : Nat) (rs : List Nat) : List Nat :=
  let known := facts n rs
  let head := heads n rs
  let forced := required n rs known
  let first := List.ofFn fun j : Fin n => entry n rs 0 j.val
  let names := first.dedup
  let options := List.ofFn fun j : Fin n =>
    let vals := match forced.getD j.val none with
      | none => names
      | some x => [x]
    vals.filter (domain n rs head j.val)
  ((fill options first).map (encode n)).filter (freshOK n rs known)

private theorem fill_mem {v left : List Nat} {opts : List (List Nat)}
    (p : v.Perm left) (allowed : List.Forall₂ (fun opt x => x∈opt) opts v) : v∈fill opts left := by
  induction allowed generalizing left with
  | nil => simp [fill]
  | @cons o a os as ha tail ih =>
    have mem := p.mem_iff.mp (List.mem_cons_self (a:=a) (l:=as))
    have rest : as.Perm (left.erase a) := by simpa using p.erase a
    exact List.mem_flatMap.mpr ⟨a,List.mem_filter.mpr ⟨ha,by simpa using mem⟩,List.mem_map.mpr ⟨as,ih rest,rfl⟩⟩

theorem supported_complete {n : Nat} [NeZero n] (m : Matrix n) (h : Laws m) (rs : List Nat)
    (f : Fits m rs) (pos : 0<rs.length) (k : Fin n) (hk : k.val=rs.length) :
    word m k∈supportedRows n rs := by
  have base (j : Fin n) : entry n rs 0 j.val=(m 0 j).val := f 0 j pos
  have perm : (List.ofFn fun j => (m k j).val).Perm (List.ofFn fun j : Fin n => entry n rs 0 j.val) := by
    simpa [List.map_ofFn,Function.comp_def,base] using (h.row_perm k).map Fin.val
  apply List.mem_filter.mpr
  refine ⟨List.mem_map.mpr ⟨_,fill_mem perm ?_,rfl⟩,(List.mem_filter.mp (next_complete h f pos k hk)).2⟩
  apply forall₂_ofFn
  intro j
  apply List.mem_filter.mpr
  constructor
  · cases e : (required n rs (facts n rs)).getD j.val none with
    | none => exact List.mem_dedup.mpr (perm.mem_iff.mp (List.mem_ofFn.mpr ⟨j,rfl⟩))
    | some x => simpa [required_allows h f pos k hk j x e]
  · apply List.all_eq_true.mpr
    intro i hi
    have len : rs.length<n := hk ▸ k.isLt
    have iLt := List.mem_range.mp hi
    let ix : Fin n := ⟨i,lt_trans iLt len⟩
    cases eq : (heads n rs).lookup (entry n rs i rs.length) with
    | none => rfl
    | some pair =>
      obtain ⟨u,v⟩ := pair
      have mem := lookup_mem eq
      simp only [heads,List.mem_flatMap,List.mem_range,List.mem_map] at mem
      obtain ⟨s,hs,t,ht,et⟩ := mem
      let sx : Fin n := ⟨s,lt_trans hs len⟩
      let tx : Fin n := ⟨t,lt_trans ht len⟩
      obtain ⟨between,tail⟩ := Prod.mk.inj et
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj tail
      have same : m ix k=m sx tx := Fin.ext ((f ix k iLt).symm.trans ((by simpa [ix,sx,tx,hk] using between.symm : entry n rs ix.val k.val=entry n rs sx.val tx.val).trans (f sx tx hs)))
      obtain ⟨z,hz⟩ := List.mem_ofFn.mp ((h.pairs _ _ _ _ same).mem_iff.mp (List.mem_ofFn.mpr ⟨j,rfl⟩))
      obtain ⟨z1,z2⟩ := Prod.mk.inj hz
      apply List.any_eq_true.mpr
      refine ⟨z.val,List.mem_range.mpr z.isLt,Bool.and_eq_true_iff.mpr ⟨?_,?_⟩⟩
      · exact beq_iff_eq.mpr ((f sx z hs).trans ((congrArg Fin.val z1).trans (f ix j iLt).symm))
      · exact beq_iff_eq.mpr ((f tx z ht).trans (congrArg Fin.val z2))

end QGI.RowCensus
