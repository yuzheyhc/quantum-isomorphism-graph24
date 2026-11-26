import RowCensus

namespace QGI.RowCensus

variable {n : Nat} [NeZero n]
abbrev Matrix (n : Nat) := Table n (Fin n)
def Fits (m : Matrix n) (rs : List Nat) :=
  ∀ i j : Fin n, i.val<rs.length → entry n rs i.val j.val = (m i j).val

private theorem extend {m : Matrix n} {rs : List Nat} (f : Fits m rs)
    (k : Fin n) (hk : k.val=rs.length) : Fits m (rs++[word m k]) := by
  intro i j hi
  by_cases smaller : i.val<rs.length
  · unfold entry
    rw [List.getD_append _ _ _ _ smaller]
    exact f i j smaller
  · have e : i=k := Fin.ext (by simp at hi; omega)
    subst i
    simp [entry,List.getD_append_right _ _ _ _ (Nat.le_of_eq hk.symm),hk]

private def weight (a : Fin n × Fin n) := 2^(5*(a.1.val*n+a.2.val))
private def tagOf (m : Matrix n) (i j : Fin n) : Tag :=
  ((m i j).val,(m j i).val, (List.ofFn (fun z => weight (m i z,m j z))).sum)

private theorem sumFn {q : Nat} (f : Fin q → Nat) : (List.ofFn f).sum=∑ i, f i := by
  induction q with
  | zero => simp
  | succ q ih => rw [List.ofFn_succ,List.sum_cons,Fin.sum_univ_succ,ih]

omit [NeZero n] in
private theorem fact_eq {m : Matrix n} {rs : List Nat} (f : Fits m rs) (i j : Fin n)
    (hi : i.val<rs.length) (hj : j.val<rs.length) : fact n rs i.val j.val=tagOf m i j := by
  unfold fact tagOf
  rw [f i j hi,f j i hj,sumFn]
  congr 2
  unfold signature
  apply Finset.sum_congr rfl
  intro z _
  exact congrArg₂ (fun a b => 2^(5*(a*n+b))) (f i z hi) (f j z hj)

private def RealTag (m : Matrix n) (v : Tag) := ∃ i j, v=tagOf m i j

private theorem agree {m : Matrix n} (h : Laws m) {v w : Tag}
    (hv : RealTag m v) (hw : RealTag m w) (eq : v.1=w.1) : v.2=w.2 := by
  obtain ⟨i,j,rfl⟩ := hv
  obtain ⟨x,y,rfl⟩ := hw
  have same : m i j=m x y := Fin.ext eq
  have perm := ((h.pairs _ _ _ _ same).map weight).sum_eq
  exact Prod.ext (congrArg Fin.val (h.reverse _ _ _ _ same))
    (by simpa [List.map_ofFn,Function.comp_def] using perm)

omit [NeZero n] in
private theorem real_facts {m : Matrix n} {rs : List Nat} (f : Fits m rs) (len : rs.length≤n) :
    ∀ v∈facts n rs, RealTag m v := by
  intro v hv
  simp only [facts,List.mem_flatMap,List.mem_range,List.mem_map] at hv
  obtain ⟨i,hi,j,hj,rfl⟩ := hv
  exact ⟨⟨i,lt_of_lt_of_le hi len⟩,⟨j,lt_of_lt_of_le hj len⟩,fact_eq f ⟨i,lt_of_lt_of_le hi len⟩ ⟨j,lt_of_lt_of_le hj len⟩ hi hj⟩

theorem lookup_mem {k : Nat} {v : Nat × Nat} {xs : List Tag} :
    xs.lookup k=some v → (k,v)∈xs := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
    rcases head with ⟨a,b⟩
    by_cases e : k=a
    · subst a; simp [List.lookup]
      intro h; exact Or.inl h.symm
    · simp [List.lookup,show (k==a)=false from beq_eq_false_iff_ne.mpr e,e,Ne.symm e]
      exact ih

private theorem lookup_consistent {m : Matrix n} (h : Laws m) {xs : List Tag}
    (good : ∀ v∈xs, RealTag m v) {v : Tag} (hv : v∈xs) : xs.lookup v.1=some v.2 := by
  induction xs with
  | nil => simp at hv
  | cons w tail ih =>
    by_cases eq : v.1=w.1
    · rcases w with ⟨a,b⟩
      have e := agree h (good v hv) (good _ List.mem_cons_self) eq
      simpa [List.lookup,eq] using congrArg some e.symm
    · have hv' : v∈tail := (List.mem_cons.mp hv).resolve_left (fun e => eq (congrArg Prod.fst e))
      rcases w with ⟨a,b⟩
      simpa [List.lookup,show (v.1==a)=false from beq_eq_false_iff_ne.mpr eq] using ih (fun t ht => good t (List.mem_cons_of_mem _ ht)) hv'

private theorem arrange_mem {v left : List Nat} {opts : List (Option Nat)}
    (p : v.Perm left) (ok : List.Forall₂ (fun o a => ∀ x, o=some x → x=a) opts v) :
    v∈arrange opts left := by
  induction ok generalizing left with
  | nil => simp [arrange]
  | @cons o a os as ha tail ih =>
    have mem : a∈left := p.mem_iff.mp List.mem_cons_self
    have rest : as.Perm (left.erase a) := by simpa using p.erase a
    simp only [arrange,List.mem_flatMap,List.mem_map]
    refine ⟨a,?_,as,ih rest,rfl⟩
    cases o with
    | none => simpa using mem
    | some x => have := ha x rfl; subst x; simp [mem]

theorem forall₂_ofFn {α β : Type} {q : Nat} (f : Fin q → α) (g : Fin q → β)
    (P : α → β → Prop) (h : ∀ i, P (f i) (g i)) : List.Forall₂ P (List.ofFn f) (List.ofFn g) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    exact .cons (h 0) (ih _ _ (fun i => h i.succ))

theorem required_allows {m : Matrix n} (h : Laws m) {rs : List Nat}
    (f : Fits m rs) (positive : 0<rs.length) (k : Fin n) (hk : k.val=rs.length) :
    ∀ j : Fin n, ∀ x, (required n rs (facts n rs)).getD j.val none=some x → x=(m k j).val := by
  have old := real_facts f (show rs.length<n from hk ▸ k.isLt).le
  intro j x eq
  have ev : (required n rs (facts n rs)).getD j.val none =
      (if j.val=rs.length then some (entry n rs 0 0) else if j.val<rs.length then
        ((facts n rs).lookup (entry n rs j.val rs.length)).map Prod.fst else none) := by
    simp [required,List.getD_eq_getElem?_getD]
  rw [ev] at eq
  by_cases a : j.val=rs.length
  · have jk : j=k := Fin.ext (a.trans hk.symm)
    subst j
    simp only [hk,if_true,Option.some.injEq] at eq
    exact eq.symm.trans ((f 0 0 positive).trans (congrArg Fin.val ((h.diagonal k k).mpr rfl).symm))
  · by_cases b : j.val<rs.length
    · simp only [if_neg a,if_pos b,Option.map_eq_some_iff] at eq
      obtain ⟨v,hv,rfl⟩ := eq
      have r := old _ (lookup_mem hv)
      have ag := agree h r (show RealTag m (tagOf m j k) from ⟨j,k,rfl⟩) (by simpa [hk] using f j k b)
      exact congrArg Prod.fst ag
    · simp [a,b] at eq

theorem next_complete {m : Matrix n} (h : Laws m) {rs : List Nat}
    (f : Fits m rs) (positive : 0<rs.length) (k : Fin n) (hk : k.val=rs.length) :
    word m k ∈ nextRows n rs := by
  let known := facts n rs
  have short : rs.length<n := hk ▸ k.isLt
  have old := real_facts f short.le
  have ex := extend f k hk
  have newLen : (rs++[word m k]).length≤n := by simp; omega
  have hnew (i : Fin n) (hi : i.val≤k.val) : i.val<(rs++[word m k]).length := by simp; omega
  have same : (List.ofFn (fun j => (m k j).val)).Perm
      (List.ofFn (fun j : Fin n => entry n rs 0 j.val)) := by
    have p := (h.row_perm k).map Fin.val
    have first (j : Fin n) : entry n rs 0 j.val=(m 0 j).val := f 0 j positive
    simpa [List.map_ofFn,Function.comp_def,first] using p
  apply List.mem_filter.mpr
  constructor
  · apply List.mem_map.mpr
    refine ⟨_,arrange_mem same ?_,rfl⟩
    unfold required
    apply forall₂_ofFn
    intro j x hx
    apply required_allows h f positive k hk j x
    simpa [required,List.getD_eq_getElem?_getD] using hx
  · unfold freshOK
    rw [List.all_eq_true]
    intro v hv
    have freshReal : ∀ t∈((List.range (rs.length+1)).flatMap fun i =>
        [fact n (rs++[word m k]) i rs.length,fact n (rs++[word m k]) rs.length i]), RealTag m t := by
      intro t ht
      simp only [List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false] at ht
      obtain ⟨i,hi,ht⟩ := ht
      let j : Fin n := ⟨i,by omega⟩
      have hj : j.val≤k.val := by dsimp [j]; omega
      rcases ht with rfl|rfl
      · exact ⟨j,k,hk ▸ fact_eq ex j k (hnew _ hj) (hnew _ le_rfl)⟩
      · exact ⟨k,j,hk ▸ fact_eq ex k j (hnew _ le_rfl) (hnew _ hj)⟩
    apply beq_iff_eq.mpr
    apply lookup_consistent h _ (List.mem_append_right _ hv)
    intro t ht
    exact (List.mem_append.mp ht).elim (old t) (freshReal t)


private theorem choices_mem {q : Nat} (opts : Fin q → List Nat) (vals : Fin q → Nat)
    (mem : ∀ j, vals j ∈ opts j) : List.ofFn vals ∈ choices (List.ofFn opts) := by
  induction q with
  | zero => simp [choices]
  | succ q ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    exact List.mem_flatMap.mpr ⟨_,mem 0,List.mem_map.mpr ⟨_,ih _ _ (fun j => mem j.succ),rfl⟩⟩

private theorem root_mem (m : Matrix n) (base : m 0 0=0) (nz : ∀ j, m 0 j=0 → j=0)
    (small : ∀ j, (m 0 j).val≤j.val) (idem : ∀ j, m 0 (m 0 j)=m 0 j) :
    word m 0 ∈ roots n := by
  unfold word roots
  apply List.mem_map.mpr
  refine ⟨_,List.mem_filter.mpr ⟨choices_mem _ _ ?_,?_⟩,rfl⟩
  · intro j
    by_cases z : j.val=0
    · have : j=0 := Fin.ext z
      subst j; simp [base]
    · simp only [if_neg z,List.mem_map,List.mem_range]
      have pos : (m 0 j).val ≠ 0 := fun eq => z (congrArg Fin.val (nz j (Fin.ext eq)))
      exact ⟨(m 0 j).val-1,by have := small j; omega,by omega⟩
  · apply List.all_eq_true.mpr
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    apply beq_iff_eq.mpr
    simpa [List.getD_eq_getElem?_getD] using congrArg Fin.val (idem j)

private theorem normalize (c : Table n Nat) (h : Laws c) :
    ∃ m : Matrix n, Laws m ∧ word m 0∈roots n ∧
      ∀ i j x y, m i j=m x y ↔ c i j=c x y := by
  classical
  let fiber (a : Nat) := Finset.univ.filter fun j : Fin n => c 0 j=a
  have occurs (i j : Fin n) : (fiber (c i j)).Nonempty := by
    have mem := (h.row_perm i).mem_iff.mp (List.mem_ofFn.mpr ⟨j,rfl⟩)
    obtain ⟨u,hu⟩ := List.mem_ofFn.mp mem
    exact ⟨u,by simpa [fiber] using hu⟩
  let g (a : Nat) : Fin n := if ha : (fiber a).Nonempty then (fiber a).min' ha else 0
  have spec (i j : Fin n) : c 0 (g (c i j)) = c i j := by
    have mem := (fiber (c i j)).min'_mem (occurs i j)
    simpa [g,occurs,fiber] using mem
  have faith (i j x y : Fin n) (eq : g (c i j)=g (c x y)) : c i j=c x y :=
    (spec i j).symm.trans ((congrArg (c 0) eq).trans (spec x y))
  let m : Matrix n := fun i j => g (c i j)
  have small (j : Fin n) : (m 0 j).val ≤ j.val := by
    have le := (fiber (c 0 j)).min'_le j (by simp [fiber])
    simpa [m,g,occurs] using le
  have base : m 0 0=0 := Fin.ext (Nat.eq_zero_of_le_zero (small 0))
  refine ⟨m,h.transport (Equiv.refl _) g faith,root_mem m base ?_ small ?_,?_⟩
  · intro j eq
    exact ((h.diagonal 0 j).mp (faith 0 j 0 0 (eq.trans base.symm))).symm
  · exact fun j => congrArg g (spec 0 j)
  · exact fun i j x y => ⟨faith i j x y,congrArg g⟩

private noncomputable def permOf (w : Nat) (inj : Mono (n:=n) w) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (mapOf n w) (Finite.injective_iff_bijective.mp inj)

theorem census_from {t : Nat} [NeZero t] (cells : Fin t → Table n Nat)
    (nodes : Array Node) (existsRoot : 0<nodes.size) (root : (nodes[0]?.getD default).rows=[])
    (optionsFor : List Nat → List Nat)
    (next : ∀ m : Matrix n, Laws m → ∀ rs, Fits m rs → 0<rs.length →
      ∀ k : Fin n, k.val=rs.length → word m k ∈ optionsFor rs)
    (cut : List Nat → Bool)
    (checked : ∀ i : Fin nodes.size, cut (nodes[i.val]?.getD default).rows || verifiedBy cells optionsFor nodes i.val)
    (finish : ∀ rs m, cut rs=true → Fits m rs → Laws m → ∃ a, Iso (cells a) m)
    (m : Matrix n) (hm : Laws m) (hr : word m 0∈optionsFor []) : ∃ a, Iso (cells a) m := by
  let node (idx : Nat) := nodes[idx]?.getD default
  have go (fuel : Nat) : ∀ (idx : Fin nodes.size) (m : Matrix n), Laws m →
      Fits m (node idx).rows → (node idx).rows.length+fuel=n →
      ((node idx).rows=[] → word m 0∈optionsFor []) → ∃ a, Iso (cells a) m := by
    induction fuel with
    | zero =>
      intro idx mat hm fits len _
      by_cases early : cut (node idx).rows=true
      · exact finish _ _ early fits hm
      simp only [Nat.add_zero] at len
      have ok : verifiedBy cells optionsFor nodes idx.val=true := (show cut (node idx).rows=true ∨ verifiedBy cells optionsFor nodes idx.val=true by simpa only [Bool.or_eq_true] using checked idx).resolve_left early
      have long : n≤(node idx).rows.length := len.ge
      simp only [verifiedBy,show n≤(nodes[idx.val]?.getD default).rows.length from long,if_true,
        decide_eq_true_eq] at ok
      obtain ⟨_,inj,iso⟩ := ok
      let p := permOf _ inj
      refine ⟨⟨(node idx).model%t,Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne t))⟩,p,fun i j x y => ?_⟩
      have f (i j : Fin n) := fits (p i) (p j) (len ▸ (p i).isLt)
      apply (iso i j x y).trans
      change (entry n (node idx).rows (p i).val (p j).val = entry n (node idx).rows (p x).val (p y).val) ↔ _
      rw [f i j,f x y,Fin.val_inj]
    | succ fuel ih =>
      intro idx mat hm fits len hr
      by_cases early : cut (node idx).rows=true
      · exact finish _ _ early fits hm
      let v := node idx
      have short : v.rows.length<n := by dsimp [v]; omega
      let k : Fin n := ⟨v.rows.length,short⟩
      let w := word mat k
      have mem : w∈optionsFor v.rows := by
        by_cases empty : v.rows=[]
        · have k0 : k=0 := Fin.ext (by simp [k,empty])
          simpa [w,k0,empty] using hr empty
        · have pos : 0<v.rows.length := List.length_pos_iff.mpr empty
          exact next mat hm v.rows fits pos k rfl
      have ok : verifiedBy cells optionsFor nodes idx.val=true := (show cut (node idx).rows=true ∨ verifiedBy cells optionsFor nodes idx.val=true by simpa only [Bool.or_eq_true] using checked idx).resolve_left early
      change (if n≤v.rows.length then _ else _) = true at ok
      rw [if_neg (Nat.not_le.mpr short)] at ok
      have check := List.all_eq_true.mp ok w mem
      change (match findMove v w with
        | none => false
        | some s => s.row==w && decide (s.child<nodes.size) && validMove n v.rows (node s.child) s) = true at check
      cases move : findMove v w with
      | none => simp [move] at check
      | some s =>
        simp only [move,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at check
        obtain ⟨⟨rowEq,childLt⟩,valid⟩ := check
        obtain ⟨lengthEq,ip,ig,acts⟩ := of_decide_eq_true valid
        let p := permOf s.points ip
        let g := permOf s.colors ig
        let child : Fin nodes.size := ⟨s.child,childLt⟩
        let m' : Matrix n := fun i j => g (mat (p i) (p j))
        have fext : Fits mat (v.rows++[s.row]) := rowEq ▸ extend fits k rfl
        have lengthChild : (node child).rows.length=v.rows.length+1 := by simpa [child,node] using lengthEq
        have fc : Fits m' (node child).rows := by
          intro i j hi
          have ht : i.val<(v.rows++[s.row]).length := by simp; rwa [lengthChild] at hi
          obtain ⟨fix,matchEq⟩ := acts i j ht
          change entry n (node child).rows i.val j.val=(g (mat (p i) (p j))).val
          have fi : p i=i := fix
          rw [fi,matchEq]
          change digit n s.colors (entry n (v.rows++[s.row]) i.val (p j).val)=_
          rw [fext i (p j) ht]
          rfl
        obtain ⟨a,e,iso⟩ := ih child m' (hm.transport p g (fun _ _ _ _ e => g.injective e)) fc
          (by change v.rows.length+fuel.succ=n at len; omega)
          (fun empty => by rw [empty] at lengthChild; simp at lengthChild)
        exact ⟨a,e.trans p,fun i j x y => (iso i j x y).trans g.injective.eq_iff⟩
  exact go n ⟨0,existsRoot⟩ m hm (by simp [node,root,Fits]) (by simp [node,root]) (fun _ => hr)

theorem census_with {t : Nat} [NeZero t] (cells : Fin t → Table n Nat)
    (nodes : Array Node) (existsRoot : 0<nodes.size) (root : (nodes[0]?.getD default).rows=[])
    (cut : List Nat → Bool)
    (checked : ∀ i : Fin nodes.size, cut (nodes[i.val]?.getD default).rows || verified cells nodes i.val)
    (finish : ∀ rs m, cut rs=true → Fits m rs → Laws m → ∃ a, Iso (cells a) m)
    (c : Table n Nat) (h : Laws c) :
    ∃ a, Iso (cells a) c := by
  obtain ⟨m,hm,hr,names⟩ := normalize c h
  obtain ⟨a,e,iso⟩ := census_from cells nodes existsRoot root
    (fun rs => if rs.isEmpty then roots n else nextRows n rs)
    (fun mat law rs f nonempty k hk => by
      have nonnil : rs≠[] := List.length_pos_iff.mp nonempty
      simpa [nonnil] using next_complete law f nonempty k hk)
    cut checked finish m hm (by simpa using hr)
  exact ⟨a,e,fun i j x y => (iso i j x y).trans (names _ _ _ _)⟩

theorem census_complete {t : Nat} [NeZero t] (cells : Fin t → Table n Nat)
    (nodes : Array Node) (existsRoot : 0<nodes.size) (root : (nodes[0]?.getD default).rows=[])
    (checked : ∀ i : Fin nodes.size, verified cells nodes i.val=true) (c : Table n Nat) (h : Laws c) :
    ∃ a, Iso (cells a) c :=
  census_with cells nodes existsRoot root (fun _ => false)
    (fun i => by simpa using checked i) (fun _ _ absurd => by cases absurd) c h

end QGI.RowCensus
