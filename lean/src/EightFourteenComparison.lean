import EightFourteenWitnesses
import AlmostFullRegion

noncomputable section
namespace QGI.Coherent.EightFourteenComparison
open EightFourteenWords EightFourteenPlacement EightFourteenWitnesses SixTenCoordinates SmallFiberExtension SmallUnion StrategyColorLaws
open FourTwelveFunctional (source)
open private bundle from SmallFiberExtension
abbrev Site := J ⊕ I
def number : Site ≃ EightFourteenWitnesses.V := finSumFinEquiv
def pts {n l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l I) (Y : Shore c r J) : Site → Fin n :=
  Sum.elim (atPoint Y) (atPoint F)
def name (a : Rep) : Site → Site → Nat
  | .inl j,.inl k => rightName (key a) j k
  | .inl j,.inr i => 16+(inside a i j).toNat
  | .inr i,.inl j => 18+(inside a i j).toNat
  | .inr i,.inr t => 20+(decide (i=t)).toNat
theorem number_read : ∀ a i j, value a (number i) (number j)=name a i j := by native_decide

private theorem mono {n l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l I) (Y : Shore c r J) (lr : l≠r) :
    Function.Injective (pts F Y) := by
  rintro (i|i) (j|j) h
  · exact congrArg Sum.inl (Y.injective (Subtype.ext h))
  · exact (lr ((F j).property.symm.trans ((congrArg (fun z => c z z) h.symm).trans (Y i).property))).elim
  · exact (lr ((F i).property.symm.trans ((congrArg (fun z => c z z) h).trans (Y j).property))).elim
  · exact congrArg Sum.inr (F.injective (Subtype.ext h))

private theorem occurs {n l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l I) (Y : Shore c r J) (z : Fin n) :
    (∃ i : EightFourteenWitnesses.V, (pts F Y ∘ number.symm) i=z) ↔ c z z=l ∨ c z z=r := by
  constructor
  · rintro ⟨i,rfl⟩
    obtain ⟨s,rfl⟩ := number.surjective i
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
    cases s with
    | inl j => exact Or.inr (Y j).property
    | inr i => exact Or.inl (F i).property
  · rintro (eq|eq)
    · exact ⟨number (.inr (F.symm ⟨z,eq⟩)),by simp [pts,atPoint]⟩
    · exact ⟨number (.inl (Y.symm ⟨z,eq⟩)),by simp [pts,atPoint]⟩

variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (p : PerfectStrategy G H K) (F : Shore (source G) l I) (Y : Shore (source G) r J)
  (T : Shore (targetName p) l I) (Z : Shore (targetName p) r J)
  {a b : Rep}

theorem solve (lr : l≠r) (keys : key a=key b)
    (read : ∀ i j x y, source G (pts F Y i) (pts F Y j)=targetName p (pts T Z x) (pts T Z y) →
      name a i j=name b x y)
    (back : a=b → ∀ i j, G.edge (pts F Y i) (pts F Y j)=H.edge (pts T Z i) (pts T Z j)) :
    AlmostFullRegion.EdgeRealizes p (fun d => d=l ∨ d=r) := by
  let reg := fun d => d=l ∨ d=r
  let f := pts F Y ∘ number.symm
  let g := pts T Z ∘ number.symm
  have eq : a=b := by
    by_contra ne
    obtain ⟨colors,arity,unequal⟩ := distinguish keys ne
    apply unequal
    have counts := Certificate.RegionalPlanar.homCount_region p (by decide : 0<22) reg f g
      ((mono F Y lr).comp number.symm.injective) ((mono T Z lr).comp number.symm.injective)
      (occurs F Y) (occurs T Z) (matrix a) (matrix b) rfl rfl .nearClique Certificate.RegionalPlanar.drawing_nearClique
      colors arity id (by
        intro i j x y same col _
        have h := read _ _ _ _ same
        simp only [EightFourteenWitnesses.read,←number_read,Equiv.apply_symm_apply] at h ⊢
        exact congrArg (fun t => t=col) h |> Iff.of_eq)
    simpa using counts
  have num {c : Fin n → Fin n → Nat} (U : Shore c l I) (W : Shore c r J) :
      ∃ h : Site ≃ Region c reg, ∀ i, (h i).val=pts U W i := by
    let h (i : Site) : Region c reg := ⟨pts U W i,(mem_vertices _ _ _).mpr ((occurs U W _).mp
      ⟨number i,by simp [Function.comp_apply]⟩)⟩
    refine ⟨Equiv.ofBijective h ⟨fun _ _ u => mono U W lr (congrArg Subtype.val u),?_⟩,fun _ => rfl⟩
    intro x; obtain ⟨j,hj⟩ := (occurs U W _).mpr ((mem_vertices _ _ _).mp x.property)
    exact ⟨number.symm j,Subtype.ext hj⟩
  obtain ⟨s,hs⟩ := num F Y
  obtain ⟨t,ht⟩ := num T Z
  change AlmostFullRegion.EdgeRealizes p reg
  have paired (u : Site) : ((s.symm.trans t) (s u)).val=pts T Z u := by
    change (t (s.symm (s u))).val=_; rw [s.symm_apply_apply,ht]
  refine ⟨s.symm.trans t,?_,?_⟩
  · intro i; obtain ⟨u,rfl⟩ := s.surjective i
    rw [paired,hs]
    cases u with
    | inl j => exact (Y j).property.trans (Z j).property.symm
    | inr i => exact (F i).property.trans (T i).property.symm
  · intro i j; obtain ⟨u,rfl⟩ := s.surjective i; obtain ⟨v,rfl⟩ := s.surjective j
    rw [paired,paired,hs,hs]
    exact back eq u v
end QGI.Coherent.EightFourteenComparison
