import AlmostFullRegion

noncomputable section
namespace QGI.Coherent.ShoreEdgeMerge
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)

private theorem number {n l k : Nat} {c : Fin n → Fin n → Nat} (A : Shore c l (Fin k)) (reg : Nat → Prop) (dis : ¬reg l) :
    ∃ e : (Fin k ⊕ Region c reg) ≃ Region c (fun v => reg v ∨ v=l),
      (∀ i, (e (.inl i)).val=atPoint A i) ∧ ∀ j, (e (.inr j)).val=j.val := by
  let f : (Fin k ⊕ Region c reg) → Region c (fun v => reg v ∨ v=l)
    | .inl i => ⟨atPoint A i,(mem_vertices _ _ _).mpr (Or.inr (A i).property)⟩
    | .inr j => ⟨j.val,(mem_vertices _ _ _).mpr (Or.inl ((mem_vertices _ _ _).mp j.property))⟩
  have apart (i : Fin k) (j : Region c reg) : atPoint A i≠j.val := fun h => dis
    ((congrArg reg (((congrArg (fun z => c z z) h).symm).trans (A i).property)).mp ((mem_vertices _ _ _).mp j.property))
  have inj : Function.Injective f := by
    rintro (i|i) (j|j) h
    · have eq : atPoint A i=atPoint A j := congrArg (Subtype.val : Region c (fun v => reg v ∨ v=l) → Fin n) h
      exact congrArg Sum.inl (A.injective (Subtype.ext eq))
    · exact (apart i j (congrArg Subtype.val h)).elim
    · exact (apart j i (congrArg Subtype.val h.symm)).elim
    · have eq : i.val=j.val := congrArg (Subtype.val : Region c (fun v => reg v ∨ v=l) → Fin n) h
      exact congrArg Sum.inr (Subtype.ext eq)
  have sur : Function.Surjective f := by
    intro x
    rcases (mem_vertices _ _ _).mp x.property with h|h
    · exact ⟨.inr ⟨x.val,(mem_vertices _ _ _).mpr h⟩,Subtype.ext rfl⟩
    · have eq : atPoint A (A.symm ⟨x.val,h⟩)=x.val := congrArg Subtype.val (A.apply_symm_apply ⟨x.val,h⟩)
      exact ⟨.inl (A.symm ⟨x.val,h⟩),Subtype.ext eq⟩
  exact ⟨Equiv.ofBijective f ⟨inj,sur⟩,fun _ => rfl,fun _ => rfl⟩

theorem join {n l k : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (F : Shore (source G) l (Fin k)) (T : Shore (targetName p) l (Fin k))
    (reg : Nat → Prop) (dis : ¬reg l)
    (e : Region (source G) reg ≃ Region (targetName p) reg)
    (old : ∀ i j, source G i.val j.val=targetName p (e i).val (e j).val)
    (within : ∀ i j, G.edge (atPoint F i) (atPoint F j)=H.edge (atPoint T i) (atPoint T j))
    (cross : ∀ i j, G.edge (atPoint F i) j.val=H.edge (atPoint T i) (e j).val) :
    AlmostFullRegion.EdgeRealizes p (fun v => reg v ∨ v=l) := by
  obtain ⟨s,sl,sr⟩ := number F reg dis
  obtain ⟨t,tl,tr⟩ := number T reg dis
  let E := s.symm.trans ((Equiv.sumCongr (Equiv.refl _) e).trans t)
  have lp (i : Fin k) : (E (s (.inl i))).val=atPoint T i := by
    simp only [E,Equiv.trans_apply,Equiv.symm_apply_apply]; exact tl i
  have rp (j : Region (source G) reg) : (E (s (.inr j))).val=(e j).val := by
    simp only [E,Equiv.trans_apply,Equiv.symm_apply_apply]; exact tr (e j)
  refine ⟨E,?_,?_⟩
  · intro x; obtain ⟨i,rfl⟩ := s.surjective x
    cases i with
    | inl i => rw [lp,sl]; exact (F i).property.trans (T i).property.symm
    | inr i => rw [rp,sr]; exact old i i
  · intro x y; obtain ⟨i,rfl⟩ := s.surjective x; obtain ⟨j,rfl⟩ := s.surjective y
    rcases i with i|i <;> rcases j with j|j <;> simp only [lp,rp,sl,sr]
    · exact within i j
    · exact cross i j
    · exact (G.symm _ _).trans ((cross j i).trans (H.symm _ _))
    · exact common_edge p (old i j)
end QGI.Coherent.ShoreEdgeMerge
