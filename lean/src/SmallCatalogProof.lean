import SmallCatalogCheck

noncomputable section
namespace QGI.SmallCatalog
open Coherent.SmallUnion CatalogComparison

theorem rowCounts :
    (List.range 13).map (fun i => (rows (i+1)).size) =
      [1,2,4,10,15,38,57,143,228,492,769,1845,2806] := by native_decide

/-- A prescribed correspondence on two unlabelled catalog entries is realized
by one point bijection. This uses no assumption about catalog coverage. -/
theorem named {n} [NeZero n] (small : n≤13) {a b : Index n} {c d : Table n}
    (hc : Configuration c) (hd : Configuration d) (C : Common c d)
    (A : Placement (frame a) c) (B : Placement (frame b) d) :
    ∃ p : Equiv.Perm (Fin n), ∀ i j, c i j=d (p i) (p j) := by
  classical
  obtain ⟨_,h⟩ := compatible hc hd C A B (positions small a) (positions small b)
  obtain rfl := same_row small h
  obtain ⟨e,he⟩ := palette C A B (positions small a) (positions small a)
  let s := model a
  have same (i j x y) : e (s.name i j)=s.name x y ↔ c (A.points i) (A.points j)=d (B.points x) (B.points y) := by
    change e ((frame a).name i j)=(frame a).name x y ↔ _
    rw [A.cell,B.cell,he,B.labels.injective.eq_iff]
  have laws : s.Laws e := by
    refine ⟨?_,?_,?_⟩
    · intro i j x y eq
      have hit := (same _ _ _ _).mp eq
      obtain ⟨left,_⟩ := CatalogComparison.ends hc hd C hit
      constructor
      · rintro rfl
        exact B.points.injective (hd.diagonal _ _ _ (hit.symm.trans left))
      · rintro rfl
        exact A.points.injective (hc.diagonal _ _ _ (hit.trans left.symm))
    · intro i j x y eq
      have hit := (same _ _ _ _).mp eq
      obtain ⟨left,_⟩ := CatalogComparison.ends hc hd C hit
      obtain ⟨p,hp⟩ := intermediate C left
      have v := hp (A.points j)
      exact (same _ _ _ _).mpr (v.2.trans (hd.reverse _ _ _ _ (v.1.symm.trans hit)))
    · intro i j x y eq
      obtain ⟨p,hp⟩ := intermediate C ((same _ _ _ _).mp eq)
      refine ⟨A.points.trans (p.trans B.points.symm),fun z => ⟨(same _ _ _ _).mpr ?_,(same _ _ _ _).mpr ?_⟩⟩
      · simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using (hp (A.points z)).1
      · simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using (hp (A.points z)).2
  obtain ⟨p,hp⟩ := Fifteen.System.check_sound (positions small a) (chain a) [] (passes small a) e laws (by simp)
  refine ⟨A.points.symm.trans (p.trans B.points),fun i j => ?_⟩
  obtain ⟨i,rfl⟩ := A.points.surjective i
  obtain ⟨j,rfl⟩ := A.points.surjective j
  simpa only [Equiv.trans_apply,Equiv.symm_apply_apply] using (same _ _ _ _).mp (hp i j)

theorem paired {n} [NeZero n] (small : n≤13) {a : Index n} {c : Table n}
    (A : Placement (frame a) c) (i j x y : Fin n) (hit : c i j=c x y) :
    ∃ e : Equiv.Perm (Fin n), e i=x ∧ e j=y ∧ ∀ u v, c u v=c (e u) (e v) := by
  obtain ⟨i,rfl⟩ := A.points.surjective i
  obtain ⟨j,rfl⟩ := A.points.surjective j
  obtain ⟨x,rfl⟩ := A.points.surjective x
  obtain ⟨y,rfl⟩ := A.points.surjective y
  rw [A.cell,A.cell,A.labels.injective.eq_iff] at hit
  obtain ⟨p,px,py,hp⟩ := transitive small a i j x y hit
  refine ⟨A.points.symm.trans (p.trans A.points),by simp [px],by simp [py],fun u v => ?_⟩
  obtain ⟨u,rfl⟩ := A.points.surjective u
  obtain ⟨v,rfl⟩ := A.points.surjective v
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply,A.cell,hp u v]

/-- A basic relation is an orbit on ordered pairs, so all the coherent
configuration axioms hold on each of the supplied representatives. -/
theorem configuration {n} [NeZero n] (small : n≤13) (a : Index n) :
    Configuration (fun i j => ((frame a).name i j).val) := by
  constructor
  · intro i j x eq
    obtain ⟨p,h₁,h₂,_⟩ := transitive small a i j x x (Fin.ext eq)
    exact p.injective (h₁.trans h₂.symm)
  · intro i j x y eq
    obtain ⟨p,h₁,h₂,h⟩ := transitive small a i j x y (Fin.ext eq)
    simpa only [h₁,h₂] using congrArg Fin.val (h j i)
  · intro s t i j x y eq
    obtain ⟨p,h₁,h₂,h⟩ := transitive small a i j x y (Fin.ext eq)
    apply Fintype.sum_equiv p
    intro z
    simp only [←h₁,←h₂,h i z,h z j]

/-- Isomorphic point/color presentations cannot have different catalog indices. -/
theorem distinct {n} [NeZero n] (small : n≤13) {a b : Index n}
    (p : Equiv.Perm (Fin n)) (e : Color a ≃ Color b)
    (h : ∀ i j, e ((frame a).name i j)=(frame b).name (p i) (p j)) : a=b := by
  let c := fun i j => ((frame a).name i j).val
  let vals (r : Nat) : Fin r ↪ Nat := ⟨Fin.val,Fin.val_injective⟩
  let A : Placement (frame a) c := ⟨Equiv.refl _,vals _,fun _ _ => rfl⟩
  let B : Placement (frame b) c := ⟨p.symm,e.symm.toEmbedding.trans (vals _),fun i j => by
    change ((frame a).name (p.symm i) (p.symm j)).val=(e.symm ((frame b).name i j)).val
    apply congrArg Fin.val
    apply e.apply_eq_iff_eq.mp
    simpa only [Equiv.apply_symm_apply] using h (p.symm i) (p.symm j)⟩
  have cfg := configuration small a
  obtain ⟨_,law⟩ := compatible cfg cfg ⟨fun _ => Iff.rfl,cfg.products⟩ A B (positions small a) (positions small b)
  exact same_row small law

end QGI.SmallCatalog

