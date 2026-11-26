import EighteenPalette
import LargeOrderHomogeneous
import HomogeneousCensus

noncomputable section
namespace QGI.EighteenPalette
open Coherent Coherent.SmallUnion Coherent.StrategyColorLaws
open private Agrees algebra equivalence homogeneous unique_map from LargeOrderHomogeneous
open Homogeneous.Unions (colorAt rawTables)
attribute [local irreducible] scheme row name

private structure Model (a : Index) (c : Table 18) where
  points : Equiv.Perm V
  labels : Fin (scheme a).rank ↪ Nat
  cell : ∀ i j, c (points i) (points j) = labels (name a i j)

private theorem model {c : Table 18} (hc : Configuration c) (hom : (algebra c hc).Homogeneous)
    (nonthin : ¬(algebra c hc).IsThin) : ∃ a, Nonempty (Model a c) := by
  classical
  obtain ⟨t,mem,F,span⟩ := Literature.hanakiMiyamoto_nonthin_census (Or.inr rfl) _ hom nonthin
  obtain ⟨a,rfl⟩ := in_archive mem
  have same (i j x y : V) : name a i j=name a x y ↔ c (F i) (F j)=c (F x) (F y) := by
    constructor
    · intro eq
      let v := c (F i) (F j)
      have inside : mark c v ∈ (algebra c hc).space := fun u w z t h => by simp only [mark,h]
      have h := (span _).mp inside i j x y (by simpa only [table_color] using congrArg Fin.val eq)
      by_cases h' : c (F x) (F y)=v
      · exact h'.symm
      · have no : (1:ℂ)=0 := by simpa only [mark,h',if_false,show c (F i) (F j)=v from rfl,if_true] using h
        exact (one_ne_zero no).elim
    · intro eq
      let v := name a i j
      let M : Mat 18 := fun z t => if name a (F.symm z) (F.symm t)=v then 1 else 0
      have inside : M ∈ (algebra c hc).space := (span _).mpr (fun u w z t h => by
        have pair : name a u w = name a z t := Fin.ext (by simpa only [table_color] using h)
        simp only [M,Equiv.symm_apply_apply,pair])
      have h := inside (F i) (F j) (F x) (F y) eq
      by_cases h' : name a x y=v
      · exact h'.symm
      · have atSource : name a i j=v := rfl
        have no : (1:ℂ)=0 := by simpa only [M,Equiv.symm_apply_apply,h',if_false,atSource,if_true] using h
        exact (one_ne_zero no).elim
  choose px py hp using onto a
  let label := fun v => c (F (px v)) (F (py v))
  have inj : Function.Injective label := fun i j h =>
    (hp i).symm.trans (((same _ _ _ _).mpr h).trans (hp j))
  exact ⟨a,⟨⟨F,⟨label,inj⟩,fun i j => (same _ _ _ _).mp (hp _).symm⟩⟩⟩

private theorem palette {a b : Index} {c d : Table 18} (A : Model a c) (B : Model b d)
    (used : ∀ v, (∃ i j, c i j=v) ↔ ∃ x y, d x y=v) :
    ∃ e : Fin (scheme a).rank ≃ Fin (scheme b).rank, ∀ i, A.labels i=B.labels (e i) := by
  have hits {a b : Index} {c d : Table 18} (S : Model a c) (T : Model b d)
      (law : ∀ v, (∃ i j, c i j=v) → ∃ x y, d x y=v) (i : Fin (scheme a).rank) :
      ∃ j, S.labels i=T.labels j := by
    obtain ⟨x,y,h⟩ := onto a i
    obtain ⟨u,v,matchColor⟩ := law _ ⟨S.points x,S.points y,(S.cell _ _).trans (congrArg S.labels h)⟩
    obtain ⟨u,rfl⟩ := T.points.surjective u
    obtain ⟨v,rfl⟩ := T.points.surjective v
    exact ⟨_,matchColor.symm.trans (T.cell _ _)⟩
  choose f hf using hits A B (fun v => (used v).mp)
  have bi : Function.Bijective f := by
    refine ⟨fun i j h => A.labels.injective ((hf i).trans ((congrArg B.labels h).trans (hf j).symm)),?_⟩
    intro j
    obtain ⟨i,hi⟩ := hits B A (fun v => (used v).mpr) j
    exact ⟨i,B.labels.injective ((hf i).symm.trans hi.symm)⟩
  exact ⟨Equiv.ofBijective f bi,hf⟩

private theorem count_named {a : Index} {c : Table 18} (S : Model a c) (i j : Fin (scheme a).rank) (x y : V) :
    count c (S.labels i) (S.labels j) (S.points x) (S.points y)=
    ∑ z : V, if name a x z=i ∧ name a z y=j then 1 else 0 := by
  rw [←count_relabel c S.points]
  simp only [count,S.cell,S.labels.injective.eq_iff]

structure Exceptional (c : Table 18) where
  points : Equiv.Perm V
  labels : Fin 8 ↪ Nat
  cell : ∀ i j, c (points i) (points j)=labels (Fin.ofNat' 8 (colorAt (row 59) i.val j.val))

private theorem row59 {a : Index} {c : Table 18} (S : Model a c) (h : a.val=59) : Nonempty (Exceptional c) := by
  have eq : a=59 := Fin.ext h
  subst a
  have rank : (scheme 59).rank=8 := by native_decide
  let fromEight : Fin 8 ≃ Fin (scheme 59).rank := finCongr rank.symm
  refine ⟨⟨S.points,fromEight.toEmbedding.trans S.labels,fun i j => (S.cell i j).trans (congrArg S.labels ?_)⟩⟩
  apply Fin.ext
  change (name 59 i j).val=colorAt (row 59) i.val j.val % 8
  rw [table_color,Nat.mod_eq_of_lt]
  exact rank ▸ (name 59 i j).isLt

/-- In homogeneous coordinates an intersection-preserving identification of
used colors carries the identity and the transpose to their counterparts. -/
private theorem diagonal_reverse {c d : Table 18} (hc : Configuration c) (hd : Configuration d)
    (left : ∀ i j, c i i=c j j) (right : ∀ i j, d i i=d j j)
    (used : ∀ s, (∃ i j, c i j=s) ↔ ∃ x y, d x y=s)
    (num : ∀ s t i j x y, c i j=d x y → count c s t i j=count d s t x y) :
    (∀ i, c i i=d i i) ∧ (∀ i j x y, c i j=d x y → c j i=d y x) := by
  have witness {s t : Nat} {i j x y : V} (eq : c i j=d x y) (z : V)
      (one : c i z=s) (two : c z j=t) : ∃ w, d x w=s ∧ d w y=t := by
    have pos : 0<count c s t i j := by
      simp only [count,Finset.sum_boole,Nat.cast_id,Finset.card_pos]
      exact ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,one,two⟩⟩
    rw [num _ _ _ _ _ _ eq] at pos
    simp only [count,Finset.sum_boole,Nat.cast_id,Finset.card_pos] at pos
    obtain ⟨w,hw⟩ := pos
    exact ⟨w,(Finset.mem_filter.mp hw).2⟩
  obtain ⟨i,j,hit⟩ := (used (d 0 0)).mpr ⟨0,0,rfl⟩
  obtain ⟨w,first,second⟩ := witness hit i (left i 0) hit
  have w0 := hd.diagonal _ _ _ second
  subst w
  have diag (v : V) := (left v 0).trans (first.symm.trans (right 0 v))
  refine ⟨diag,fun i j x y eq => ?_⟩
  obtain ⟨z,a,b⟩ := witness ((diag i).trans (right i x)) j rfl rfl
  exact b.symm.trans (hd.reverse _ _ _ _ (a.trans eq))

/-- The table at one-based position 60 is the only possible home of an
unrealized palette identification. Only the nonthin census is used for coverage. -/
theorem position {c d : Table 18} (hc : Configuration c) (hd : Configuration d)
    (left : ∀ i j, c i i=c j j) (right : ∀ i j, d i i=d j j)
    (used : ∀ s, (∃ i j, c i j=s) ↔ ∃ x y, d x y=s)
    (num : ∀ s t i j x y, c i j=d x y → count c s t i j=count d s t x y) :
    (∃ h : Equiv.Perm V, ∀ i j, c i j=d (h i) (h j)) ∨ Nonempty (Exceptional c) ∧ Nonempty (Exceptional d) := by
  classical
  obtain ⟨diag,rev⟩ := diagonal_reverse hc hd left right used num
  let L := equivalence hc hd used num diag rev
  have hom := homogeneous hc (by decide) left
  by_cases thin : (algebra c hc).IsThin
  · obtain ⟨m,hm⟩ := Literature.muzychukPonomarenko_thin_separable (by decide) hom thin L
    refine Or.inl ⟨m,fun i j => ?_⟩
    let v := c i j
    have mem : mark c v ∈ (algebra c hc).space := fun u w x y h => by simp only [mark,h]
    have both : Agrees c d (mark c v) (mark d v) := fun u w x y h => by simp only [mark,h]
    have im : L.map (mark c v)=mark d v := unique_map (fun x y => (used _).mpr ⟨x,y,rfl⟩) both
    have h := hm _ mem i j
    rw [im] at h
    by_contra ne
    simpa [mark,v,Ne.symm ne] using h
  obtain ⟨a,⟨A⟩⟩ := model hc hom thin
  obtain ⟨b,⟨B⟩⟩ := model hd (L.homogeneous_target hom) (fun h => thin (L.thin_iff.mpr h))
  obtain ⟨e,labels⟩ := palette A B used
  have same (i j x y : V) : e (name a i j)=name b x y ↔ c (A.points i) (A.points j)=d (B.points x) (B.points y) := by
    rw [A.cell,B.cell,labels,B.labels.injective.eq_iff]
  obtain ⟨profile,listed⟩ := eligible a b e (fun i j x y h =>
    (same _ _ _ _).mpr (rev _ _ _ _ ((same _ _ _ _).mp h))) (fun i j x y h s t => by
      have ok := num (A.labels s) (A.labels t) _ _ _ _ ((same i j x y).mp h)
      rw [count_named A,labels s,labels t,count_named B] at ok
      exact ok)
  rcases classify a b e profile listed with ⟨f,h⟩|⟨ha,hb⟩
  · refine Or.inl ⟨A.points.symm.trans (f.trans B.points),fun i j => ?_⟩
    obtain ⟨i,rfl⟩ := A.points.surjective i
    obtain ⟨j,rfl⟩ := A.points.surjective j
    simpa only [Equiv.trans_apply,Equiv.symm_apply_apply] using (same _ _ _ _).mp (h i j)
  · exact Or.inr ⟨row59 A ha,row59 B hb⟩

end QGI.EighteenPalette
