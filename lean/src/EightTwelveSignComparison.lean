import EightTwelveSignLaws

noncomputable section
namespace QGI.Coherent.EightTwelveSignComparison
open EightTwelveSigns SixTenCoordinates SmallFiberExtension SmallUnion StrategyColorLaws
open FourTwelveFunctional (source)
open private bundle from SmallFiberExtension
abbrev Site := J ⊕ I
def number : Site ≃ EightTwelveSigns.V := finSumFinEquiv
def pts {n l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l I) (Y : Shore c r J) : Site → Fin n :=
  Sum.elim (atPoint Y) (atPoint F)
def name (a : Rep) : Site → Site → Nat
  | .inl j,.inl k => rightName (key a) j k
  | .inl j,.inr i => 16+(inside a i j).toNat
  | .inr i,.inl j => 18+(inside a i j).toNat
  | .inr i,.inr t => 20+rowOverlap a i t
theorem number_read : ∀ a i j, value a (number i) (number j)=name a i j := by native_decide

private theorem mono {n l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l I) (Y : Shore c r J) (lr : l≠r) :
    Function.Injective (pts F Y) := by
  rintro (i|i) (j|j) h
  · exact congrArg Sum.inl (Y.injective (Subtype.ext h))
  · exact (lr ((F j).property.symm.trans ((congrArg (fun z => c z z) h.symm).trans (Y i).property))).elim
  · exact (lr ((F i).property.symm.trans ((congrArg (fun z => c z z) h).trans (Y j).property))).elim
  · exact congrArg Sum.inr (F.injective (Subtype.ext h))

private theorem occurs {n l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l I) (Y : Shore c r J) (z : Fin n) :
    (∃ i : EightTwelveSigns.V, (pts F Y ∘ number.symm) i=z) ↔ c z z=l ∨ c z z=r := by
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
    (back : a=b → ∀ i j, source G (pts F Y i) (pts F Y j)=targetName p (pts T Z i) (pts T Z j))
    (reg : Nat → Prop) (cover : ∀ z, reg (source G z z) → source G z z=l ∨ source G z z=r) : Realizes p reg := by
  let reg' := fun t => t=l ∨ t=r
  let f := pts F Y ∘ number.symm
  let g := pts T Z ∘ number.symm
  have eq : a=b := by
    by_contra ne
    obtain ⟨pat,colors,draw,arity,unequal⟩ := distinguish keys ne
    apply unequal
    have counts := Certificate.RegionalPlanar.homCount_region p (by decide : 0<20) reg' f g
      ((mono F Y lr).comp number.symm.injective) ((mono T Z lr).comp number.symm.injective)
      (occurs F Y) (occurs T Z) (matrix a) (matrix b) rfl rfl pat draw colors arity id (by
        intro i j x y same col _
        have h := read _ _ _ _ same
        simp only [EightTwelveSigns.read,←number_read,Equiv.apply_symm_apply] at h ⊢
        exact congrArg (fun t => t=col) h |> Iff.of_eq)
    simpa using counts
  have pick (z : Region (source G) reg) := (occurs F Y z.val).mpr (cover _ ((mem_vertices _ _ _).mp z.property))
  choose h hh using pick
  have both (i j) : source G i.val j.val=targetName p (g (h i)) (g (h j)) := by
    rw [←hh i,←hh j]
    exact back eq _ _
  obtain ⟨e,he⟩ := bundle p reg (fun i => g (h i)) both
  exact ⟨e,fun i j => by rw [he,he]; exact both i j⟩

end QGI.Coherent.EightTwelveSignComparison
