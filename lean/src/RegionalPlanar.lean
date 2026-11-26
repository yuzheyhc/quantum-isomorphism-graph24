import ColoredPlanarWitness
import StrategyColorLaws

noncomputable section
open scoped BigOperators

namespace QGI.Certificate.RegionalPlanar
open Coherent Coherent.StrategyColorLaws

variable {n k : Nat} {G H : Graph n} {K : Type}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (p : PerfectStrategy G H K)

private abbrev c := Relations.color (closure G)

private theorem on_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s t : ℂ) :
    s • (0 : E →L[ℂ] E) = t • (0 : E →L[ℂ] E) := by simp

private theorem incompatible (x y a b : Fin n)
    (different : c (G:=G) x y ≠ targetName p a b) :
    ColorTensor.P p x a * ColorTensor.P p y b = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply ColorTensor.product_zero p (mark_intertwines p (c (G:=G) x y)) x y a b _ v
  simp [mark,c,Ne.symm different]

private theorem outside (x a : Fin n) (different : c (G:=G) x x ≠ targetName p a a) :
    ColorTensor.P p x a = 0 :=
  ((ColorTensor.quantumPermutation p).1 x a).1.symm.trans (incompatible p x x a a different)

/-- Restrict the actual quantum permutation to a union of matched diagonal colors
and independently number the two copies. The colors of the two supplied finite
tables may use their own numeric names. -/
theorem homCount_region (positive : 0 < k) (region : Nat → Prop)
    (f g : Fin k → Fin n) (hf : Function.Injective f) (hg : Function.Injective g)
    (src : ∀ z, (∃ i, f i=z) ↔ region (Relations.color (closure G) z z))
    (tgt : ∀ z, (∃ i, g i=z) ↔ region (targetName p z z))
    (m t : ColorMatrix) (hm : m.order=k) (ht : t.order=k)
    (pat : Pattern) (draw : ∃ v : Array PlanePoint, Draws pat v)
    (colors : List Nat) (arity : colors.length=pat.edges.length) (rename : Nat → Nat)
    (named : ∀ i j a b, Relations.color (closure G) (f i) (f j) = targetName p (g a) (g b) →
      ∀ s ∈ colors, (m.get i.val j.val = s ↔ t.get a.val b.val = rename s)) :
    homCount m pat colors = homCount t pat (colors.map rename) := by
  let U := fun i a => ColorTensor.P p (f i) (g a)
  obtain ⟨proj,rows,cols⟩ := ColorTensor.quantumPermutation p
  have row (i : Fin k) : ∑ a, U i a = 1 := by
    apply Eq.trans _ (rows (f i))
    apply Fintype.sum_of_injective g hg (U i) (ColorTensor.P p (f i)) _ (fun _ => rfl)
    intro z out
    apply outside p
    intro eq
    exact out ((tgt z).mpr (eq ▸ ((src (f i)).mp ⟨i,rfl⟩)))
  have col (a : Fin k) : ∑ i, U i a = 1 := by
    apply Eq.trans _ (cols (g a))
    apply Fintype.sum_of_injective f hf (fun i => U i a) (fun z => ColorTensor.P p z (g a)) _ (fun _ => rfl)
    intro z out
    apply outside p
    intro eq
    apply out
    apply (src z).mpr
    change region (c (G:=G) z z)
    rw [eq]
    exact (tgt (g a)).mp ⟨a,rfl⟩
  rw [homCount_eq_binaryCspCount,homCount_eq_binaryCspCount]
  apply Literature.caiYoung_binary_planar positive m t hm ht pat draw colors arity rename
    U (fun i a => proj (f i) (g a)) row col
  intro s hs i j
  calc
    _ = ∑ a, ∑ b, (binary m s i j : ℂ) • (U i a * U j b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases eq : Relations.color (closure G) (f i) (f j) = targetName p (g a) (g b)
      · simp only [binary,named i j a b eq s hs]
      · have zero : U i a * U j b = 0 := incompatible p _ _ _ _ eq
        rw [zero]
        exact on_zero (E:=ColorTensor.space p) _ _
    _ = (binary m s i j : ℂ) • 1 := by
      simp_rw [← Finset.smul_sum,← Finset.mul_sum,row,mul_one]
      rw [row i]

set_option maxRecDepth 2000 in
theorem drawing_nearClique : ∃ v : Array PlanePoint, Draws .nearClique v := by
  exact ⟨#[(0,0),(1,2),(20,0),(0,20),(1,1)], by unfold Draws; decide⟩

abbrev fourteenColors : List Nat := [7,5,4,3,10,10,4,5,10]

/-- All four published archive rows have the same source colors and report 24 vs 0. -/
theorem exclude_fourteen (region : Nat → Prop) (f g : Fin 14 → Fin n)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (src : ∀ z, (∃ i, f i=z) ↔ region (Relations.color (closure G) z z))
    (tgt : ∀ z, (∃ i, g i=z) ↔ region (targetName p z z))
    (perm : List Nat)
    (checked : check m_fourteen_249 m_fourteen_249 .nearClique perm fourteenColors 24 0=true)
    (named : ∀ i j a b, Relations.color (closure G) (f i) (f j) = targetName p (g a) (g b) →
      ∀ s ∈ fourteenColors, (m_fourteen_249.get i.val j.val = s ↔
        m_fourteen_249.get a.val b.val = perm[s]?.getD m_fourteen_249.rank)) : False := by
  exact counts_differ_of_checked checked (homCount_region p (by decide) region f g hf hg src tgt
    m_fourteen_249 m_fourteen_249 rfl rfl .nearClique drawing_nearClique fourteenColors rfl _ named)

end QGI.Certificate.RegionalPlanar
