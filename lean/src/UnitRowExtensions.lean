import RowPredictions

namespace QGI.RowCensus

private def renamed (n r : Nat) (names targets : List Nat) :=
  let pairs := names.zip targets
  encode n ((wordDigits n r).map fun a => (pairs.lookup a).getD 0)

private def pivot (n : Nat) (rs : List Nat) := (List.range rs.length).find? fun i =>
  (wordDigits n (rs.getD 0 0)).count (entry n rs i rs.length)==1

private def extra (n : Nat) (rs : List Nat) (w : Nat) :=
  digit n w rs.length == entry n rs 0 0 &&
  decide ((wordDigits n w).Perm (wordDigits n (rs.getD 0 0))) &&
  freshOK n rs (facts n rs) w && balancedNext n rs w

open private fill fill_mem from RowSupports

/-- A thin edge renames colors without changing their valencies. The diagonal
and any known transposes can constrain a name before its image is tried. -/
private def paletteOptions (n : Nat) (rs : List Nat) (r : Nat) (ns : List Nat) :=
  let first := wordDigits n (rs.getD 0 0)
  let must := required n rs (facts n rs)
  ns.map fun a => ns.filter fun b => first.count a==first.count b &&
    (List.range n).all fun z => digit n r z != a || (must.getD z none).all (· == b)

def unitRows (n : Nat) (rs : List Nat) : List Nat :=
  match (predict n rs).lookup rs.length with
  | some w => if extra n rs w then [w] else []
  | none => match pivot n rs with
    | none => balancedRows n rs
    | some i =>
      let r := rs.getD i 0
      let names := (wordDigits n r).dedup
      ((fill (paletteOptions n rs r names) names).map (renamed n r names)).filter (extra n rs)

private theorem zip_of_map (ns : List Nat) (g : Nat → Nat) :
    ns.zip (ns.map g)=ns.map (fun a => (a,g a)) := by induction ns <;> simp [*]

theorem unit_complete {n : Nat} [NeZero n] (m : Matrix n) (h : Laws m) (rs : List Nat)
    (f : Fits m rs) (pos : 0<rs.length) (k : Fin n) (hk : k.val=rs.length) : word m k∈unitRows n rs := by
  classical
  have first (j : Fin n) : digit n (rs.getD 0 0) j.val=(m 0 j).val := f 0 j pos
  have rows (i : Fin n) : (List.ofFn fun z => (m i z).val).Perm (wordDigits n (rs.getD 0 0)) := by
    simpa only [wordDigits,List.map_ofFn,Function.comp_def,first] using (h.row_perm i).map Fin.val
  have extraOK : extra n rs (word m k)=true := by
    have e : digit n (word m k) rs.length=(m k k).val := hk ▸ digit_word m k k
    have d : (m k k).val=entry n rs 0 0 := (congrArg Fin.val ((h.diagonal k k).mpr rfl)).trans (f 0 0 pos).symm
    have p : (wordDigits n (word m k)).Perm (wordDigits n (rs.getD 0 0)) := by simpa [wordDigits,first] using rows k
    simp only [extra,e,d,beq_self_eq_true,decide_eq_true p,Bool.true_and]
    exact Bool.and_eq_true_iff.mpr ⟨(List.mem_filter.mp (next_complete h f pos k hk)).2,
      (List.mem_filter.mp (balanced_complete m h rs f pos k hk)).2⟩
  have short : rs.length<n := hk ▸ k.isLt
  unfold unitRows
  cases get : (predict n rs).lookup rs.length with
  | some w =>
    obtain ⟨v,hv⟩ := predict_sound m h rs f pos short.le _ (lookup_in get)
    obtain ⟨v0,rfl⟩ := Prod.mk.inj hv
    have vk : v=k := Fin.ext (v0.symm.trans hk.symm)
    simpa [vk,extraOK]
  | none =>
    cases piv : pivot n rs with
    | none => exact balanced_complete m h rs f pos k hk
    | some i =>
      have mem := List.mem_range.mp (List.mem_of_find?_eq_some piv)
      let v : Fin n := ⟨i,lt_trans mem short⟩
      have val (j : Fin n) : digit n (rs.getD i 0) j.val=(m v j).val := f v j mem
      have thinTest := List.find?_some piv
      have one : degree m (m v k)=1 := by
        have atK : entry n rs i rs.length=(m v k).val := hk ▸ f v k mem
        simpa only [wordDigits,first,atK,beq_iff_eq,countFiber,Fin.val_inj,degree,fiber] using thinTest
      have tu := thin_degree h v k one
      have tv := thin_degree h k v ((degree_reverse h k v).trans one)
      have same (x y : Fin n) : m v x=m v y ↔ m k x=m k y :=
        ⟨fun eq => rename_one h v k v k x y tu rfl eq,fun eq => rename_one h k v k v x y tv rfl eq⟩
      let g (a : Nat) := if ha : ∃ x, (m v x).val=a then (m k ha.choose).val else a
      have acts (x : Fin n) : g (m v x).val=(m k x).val := by
        have e : ∃ y, (m v y).val=(m v x).val := ⟨x,rfl⟩
        exact (dif_pos e).trans (congrArg Fin.val ((same _ _).mp (Fin.ext e.choose_spec)))
      let ns := (wordDigits n (rs.getD i 0)).dedup
      have inside (a : Nat) : a∈ns ↔ ∃ z, (m v z).val=a := by simp only [ns,wordDigits,List.mem_dedup,List.mem_ofFn,val]
      have sameRange (a : Nat) : (∃ z, (m v z).val=a) ↔ ∃ z, (m k z).val=a := by
        simpa only [← List.mem_ofFn] using ((rows v).trans (rows k).symm).mem_iff (a:=a)
      have noDup : ns.Nodup := List.nodup_dedup _
      have distinct : (ns.map g).Nodup := (List.nodup_map_iff_inj_on noDup).mpr (by
        intro a ha b hb eq
        obtain ⟨x,rfl⟩ := (inside a).mp ha
        obtain ⟨y,rfl⟩ := (inside b).mp hb
        rw [acts,acts] at eq
        exact congrArg Fin.val ((same x y).mpr (Fin.ext eq)))
      have perm : (ns.map g).Perm ns := (List.perm_ext_iff_of_nodup distinct noDup).mpr (by
        intro a
        constructor
        · intro ha
          obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
          obtain ⟨x,rfl⟩ := (inside _).mp hb
          exact (inside _).mpr ((sameRange _).mpr ⟨x,(acts x).symm⟩)
        · intro ha
          obtain ⟨x,hx⟩ := (sameRange a).mp ((inside a).mp ha)
          exact List.mem_map.mpr ⟨_,(inside _).mpr ⟨x,rfl⟩,(acts x).trans hx⟩)
      have allowed (a : Nat) (ha : a∈ns) :
          g a∈ns.filter (fun b => (wordDigits n (rs.getD 0 0)).count a == (wordDigits n (rs.getD 0 0)).count b &&
            (List.range n).all fun z => digit n (rs.getD i 0) z != a ||
              ((required n rs (facts n rs)).getD z none).all (· == b)) := by
        obtain ⟨x,rfl⟩ := (inside a).mp ha
        have valency : degree m (m v x)=degree m (m k x) := by
          rw [←fiber_card h v,←fiber_card h k]
          congr 1
          ext z
          exact (by simp only [fiber,Finset.mem_filter,Finset.mem_univ,true_and]; exact same z x)
        have cnt (b : Fin n) : (wordDigits n (rs.getD 0 0)).count b.val=degree m b := by
          simp only [wordDigits,first,countFiber,Fin.val_inj,degree,fiber]
        refine List.mem_filter.mpr ⟨perm.mem_iff.mp (List.mem_map.mpr ⟨_,(inside _).mpr ⟨x,rfl⟩,rfl⟩),
          Bool.and_eq_true_iff.mpr ⟨by rw [acts,cnt,cnt,valency]; simp,?_⟩⟩
        apply List.all_eq_true.mpr
        intro z hz
        let y : Fin n := ⟨z,List.mem_range.mp hz⟩
        by_cases equiv : m v y=m v x
        · cases eq : (required n rs (facts n rs)).getD z none with
          | none => simp
          | some b =>
            have forced := required_allows h f pos k hk y b eq
            simp [forced,acts,(same y x).mp equiv]
        · have diff : digit n (rs.getD i 0) z != (m v x).val := by
            exact bne_iff_ne.mpr (fun e => equiv (Fin.ext ((val y).symm.trans e)))
          exact Bool.or_eq_true_iff.mpr (Or.inl diff)
      have allowedAll : List.Forall₂ (fun opt b => b∈opt) (paletteOptions n rs (rs.getD i 0) ns) (ns.map g) := by
        unfold paletteOptions
        apply List.forall₂_map_left_iff.mpr
        apply List.forall₂_map_right_iff.mpr
        exact List.forall₂_same.mpr allowed
      apply List.mem_filter.mpr
      refine ⟨List.mem_map.mpr ⟨_,fill_mem perm allowedAll,?_⟩,extraOK⟩
      unfold renamed
      rw [zip_of_map]
      apply congrArg (encode n)
      simp only [wordDigits,List.map_ofFn,Function.comp_def,val]
      apply congrArg List.ofFn
      funext j
      have memJ := (inside _).mpr ⟨j,rfl⟩
      have hit := lookup_of_occurrence (xs:=ns.map fun a => (a,g a)) (a:=(m v j).val)
        (b:=g (m v j).val) ⟨_,List.mem_map.mpr ⟨_,memJ,rfl⟩⟩ (by
          intro b hb
          obtain ⟨a,_,eq⟩ := List.mem_map.mp hb
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
          rfl)
      simp only [ns,wordDigits,val] at hit
      rw [hit]; exact acts j

end QGI.RowCensus
