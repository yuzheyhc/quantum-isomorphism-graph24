import LargeOrderSingleCensus
import LargeOrderHomogeneous

noncomputable section
namespace QGI.LargeOrderSingle
open Coherent Coherent.SmallUnion Coherent.StrategyColorLaws Coherent.LargeFourteenRegion
open Coherent.LargeOrderHomogeneous
open Coherent.FourTwelveFunctional (source)
open private Agrees algebra equivalence homogeneous unique_map from LargeOrderHomogeneous
open Homogeneous.Unions (colorAt rawTables)
attribute [local irreducible] scheme row name

private structure Model (a : Index) (c : Table 16) where
  points : Equiv.Perm V
  labels : Fin (scheme a).rank ↪ Nat
  cell : ∀ i j, c (points i) (points j) = labels (name a i j)

private theorem model {c : Table 16} (hc : Configuration c) (hom : (algebra c hc).Homogeneous)
    (nonthin : ¬(algebra c hc).IsThin) : ∃ a, Nonempty (Model a c) := by
  classical
  obtain ⟨t,mem,F,span⟩ := Literature.hanakiMiyamoto_nonthin_census (Or.inl rfl) _ hom nonthin
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
      let M : Mat 16 := fun z t => if name a (F.symm z) (F.symm t)=v then 1 else 0
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

private theorem palette {a b : Index} {c d : Table 16} (A : Model a c) (B : Model b d)
    (used : ∀ v, (∃ i j, c i j=v) ↔ ∃ x y, d x y=v) :
    ∃ e : Fin (scheme a).rank ≃ Fin (scheme b).rank, ∀ i, A.labels i=B.labels (e i) := by
  have hits {a b : Index} {c d : Table 16} (S : Model a c) (T : Model b d)
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

private theorem count_named {a : Index} {c : Table 16} (S : Model a c) (i j : Fin (scheme a).rank) (x y : V) :
    count c (S.labels i) (S.labels j) (S.points x) (S.points y)=
    ∑ z : V, if name a x z=i ∧ name a z y=j then 1 else 0 := by
  rw [←count_relabel c S.points]
  simp only [count,S.cell,S.labels.injective.eq_iff]

private theorem reindex {n} (f : V → Fin n) (e : Equiv.Perm V) (x : Fin n) :
    (∃ i, (f ∘ e) i=x) ↔ ∃ i, f i=x :=
  ⟨fun ⟨i,h⟩ => ⟨e i,h⟩,fun ⟨i,h⟩ => ⟨e.symm i,by simpa using h⟩⟩

/-- The thin case is separable. For all 208 nonthin source schemes both
catalog placements retain the actual palette correspondence of the region. -/
theorem solve {n} {G H : QGI.Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) {reg : Nat → Prop} (f g : V → Fin n)
    (D : DataFor p reg f g) (single : ∀ i j, source G (f i) (f i)=source G (f j) (f j)) :
    ∃ h : Equiv.Perm V, ∀ i j, source G (f i) (f j)=targetName p (g (h i)) (g (h j)) := by
  classical
  let c := restricted (source G) f
  let d := restricted (targetName p) g
  let L := equivalence (c:=c) (d:=d) D.srcConfig D.tgtConfig D.used D.products D.sameDiag
    (fun _ _ _ _ h => common_transpose p h)
  have hom := homogeneous D.srcConfig (by decide) single
  by_cases thin : (algebra c D.srcConfig).IsThin
  · obtain ⟨m,hm⟩ := Literature.muzychukPonomarenko_thin_separable (by decide) hom thin L
    refine ⟨m,fun i j => ?_⟩
    let v := c i j
    have mem : mark c v ∈ (algebra c D.srcConfig).space := fun u w z t h => by simp only [mark,h]
    have both : Agrees c d (mark c v) (mark d v) := fun x y u w h => by simp only [mark,h]
    have im : L.map (mark c v)=mark d v := unique_map (fun x y => (D.used _).mpr ⟨x,y,rfl⟩) both
    have h := hm _ mem i j
    rw [im] at h
    by_cases eq : d (m i) (m j)=v
    · exact eq.symm
    · have no : (1:ℂ)=0 := by simpa only [mark,eq,if_false,show c i j=v from rfl,if_true] using h
      exact (one_ne_zero no).elim
  obtain ⟨a,⟨A⟩⟩ := model D.srcConfig hom thin
  obtain ⟨b,⟨B⟩⟩ := model D.tgtConfig (L.homogeneous_target hom) (fun h => thin (L.thin_iff.mpr h))
  obtain ⟨e,labels⟩ := palette A B D.used
  have same (i j x y : V) : e (name a i j)=name b x y ↔
      c (A.points i) (A.points j)=d (B.points x) (B.points y) := by
    change _ ↔ restricted (source G) f _ _=restricted (targetName p) g _ _
    rw [A.cell,B.cell,labels,B.labels.injective.eq_iff]
  obtain ⟨ranks,profile,listed⟩ := eligible a b e (fun i j x y h =>
    (same _ _ _ _).mpr (common_transpose p ((same _ _ _ _).mp h))) (fun i j x y h s t => by
      have ok := D.products (A.labels s) (A.labels t) _ _ _ _ ((same i j x y).mp h)
      rw [count_named A,labels s,labels t,count_named B] at ok
      exact ok)
  rcases dichotomy a b e ranks profile listed with ⟨h,point⟩ | ⟨r,hr,key,valid,diff⟩
  · refine ⟨A.points.symm.trans (h.trans B.points),fun i j => ?_⟩
    obtain ⟨i,rfl⟩ := A.points.surjective i
    obtain ⟨j,rfl⟩ := A.points.surjective j
    simpa only [Equiv.trans_apply,Equiv.symm_apply_apply] using (same _ _ _ _).mp (point i j)
  · exact False.elim (exclude p reg (f ∘ A.points) (g ∘ B.points)
      (D.injF.comp A.points.injective) (D.injG.comp B.points.injective)
      (fun z => (reindex f A.points z).trans (D.src z)) (fun z => (reindex g B.points z).trans (D.tgt z))
      a b e (fun i j x y => (same i j x y).mpr) r hr key valid diff)

end QGI.LargeOrderSingle
