import LargeOrderBlocks
import RegionalPlanar
import HomogeneousUnions

noncomputable section
namespace QGI.LargeOrderNineteen
open Coherent Coherent.SmallUnion Homogeneous.Unions

/-- False selects the second scheme and true selects the third in the
one-based Hanaki–Miyamoto archive. The two non-diagonal colors are directed. -/
def matrix (a : Bool) : Certificate.ColorMatrix :=
  let t := (rawTables 19)[if a then 2 else 1]?.getD #[]
  ⟨19,3,Array.ofFn fun i : Fin 361 => colorAt t (i.val/19) (i.val%19)⟩

abbrev V := Fin 19
def name (a : Bool) (i j : V) := Fin.ofNat' 3 ((matrix a).get i.val j.val)
private theorem order (a : Bool) : (matrix a).order=19 := rfl

structure Presentation (a : Bool) (c : Coherent.SmallUnion.Table 19) where
  points : Equiv.Perm V
  labels : Fin 3 ↪ Nat
  cell : ∀ i j, c (points i) (points j)=labels (name a i j)

def arcs : List Nat := [1,1,1,1,1,1,1,2,1]
def flip (k : Nat) : Nat := if k=1 then 2 else if k=2 then 1 else k

theorem counts : ∀ a : Bool,
    Certificate.homCount (matrix a) .nearClique arcs=(if a then 3762 else 3654) ∧
    Certificate.homCount (matrix a) .nearClique (arcs.map flip)=(if a then 3762 else 3654) := by
  native_decide

private theorem rows : ∀ a : Bool, (∀ k : Fin 3, ∃ i j, name a i j=k) ∧
    (∀ i, name a i i=0) ∧ ∀ i j, (matrix a).get i.val j.val=(name a i j).val := by native_decide
end QGI.LargeOrderNineteen

namespace QGI.Literature
open Coherent.SmallUnion Coherent.StrategyColorLaws LargeOrderNineteen

/-- Ziv-Av, Table 2, page 67, lists {2,3} as the only class of distinct
algebraically isomorphic schemes of order nineteen. Table 3, page 68, lists
no scheme of this order with a proper algebraic automorphism. Applying an
ordinary identification to a pair of the same type therefore realizes the
specified correspondence. The remaining alternative supplies exactly the
original catalog positions, in either order and up to point and color names.
https://actamath.savbb.sk/pdf/aumb2605.pdf
https://sites.google.com/view/small-association-schemes -/
axiom zivAv_nineteen_catalog_positions {c d : Table 19} (src : Configuration c) (tgt : Configuration d)
    (hom : ∀ i j, c i i=c j j) (hom' : ∀ i j, d i i=d j j)
    (used : ∀ a, (∃ i j, c i j=a) ↔ ∃ x y, d x y=a)
    (numbers : ∀ a b i j x y, c i j=d x y → count c a b i j=count d a b x y) :
    (∃ h : Equiv.Perm V, ∀ i j, c i j=d (h i) (h j)) ∨
      ∃ a : Bool, Nonempty (Presentation a c) ∧ Nonempty (Presentation (!a) d)
end QGI.Literature

namespace QGI.LargeOrderNineteen
open Coherent Coherent.SmallUnion Coherent.StrategyColorLaws Coherent.LargeFourteenRegion Certificate
open Coherent.FourTwelveFunctional (source)
attribute [local irreducible] matrix

private theorem reindex {n} (f : V → Fin n) (e : Equiv.Perm V) (x : Fin n) :
    (∃ i, (f ∘ e) i=x) ↔ ∃ i, f i=x :=
  ⟨fun ⟨i,h⟩ => ⟨e i,h⟩,fun ⟨i,h⟩ => ⟨e.symm i,by simpa using h⟩⟩

theorem solve {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) {reg : Nat → Prop} (f g : V → Fin n)
    (D : DataFor p reg f g) (single : ∀ i j, source G (f i) (f i)=source G (f j) (f j)) :
    ∃ h : Equiv.Perm V, ∀ i j, source G (f i) (f j)=targetName p (g (h i)) (g (h j)) := by
  classical
  let c := restricted (source G) f
  let d := restricted (targetName p) g
  have other (i j) : d i i=d j j := (D.sameDiag i).symm.trans ((single i j).trans (D.sameDiag j))
  rcases Literature.zivAv_nineteen_catalog_positions D.srcConfig D.tgtConfig single other D.used D.products with
    yes | ⟨a,⟨A⟩,⟨B⟩⟩
  · exact yes
  have hits (i : Fin 3) : ∃ j, A.labels i=B.labels j := by
    obtain ⟨x,y,h⟩ := (rows a).1 i
    obtain ⟨u,v,hv⟩ := (D.used _).mp ⟨A.points x,A.points y,(A.cell x y).trans (congrArg A.labels h)⟩
    obtain ⟨u,rfl⟩ := B.points.surjective u
    obtain ⟨v,rfl⟩ := B.points.surjective v
    exact ⟨_,hv.symm.trans (B.cell u v)⟩
  choose e labels using hits
  have inj : Function.Injective e := fun i j h =>
    A.labels.injective ((labels i).trans ((congrArg B.labels h).trans (labels j).symm))
  have zero : e 0=0 := by
    apply B.labels.injective
    have h := (A.cell 0 0).symm.trans ((D.sameDiag (A.points 0)).trans ((other (A.points 0) (B.points 0)).trans (B.cell 0 0)))
    simpa only [(rows a).2.1,(rows (!a)).2.1,labels] using h
  have cases3 : (∀ v, (e v).val=v.val) ∨ (∀ v, (e v).val=flip v.val) := by
    have e1 : e 1≠0 := fun h => (by decide : (1 : Fin 3)≠0) (inj (h.trans zero.symm))
    have e2 : e 2≠0 := fun h => (by decide : (2 : Fin 3)≠0) (inj (h.trans zero.symm))
    have diff : e 1≠e 2 := fun h => (by decide : (1 : Fin 3)≠2) (inj h)
    rcases (show ∀ i j : Fin 3, i≠0 → j≠0 → i≠j → (i=1 ∧ j=2) ∨ (i=2 ∧ j=1) by decide) _ _ e1 e2 diff with
      ⟨i,j⟩ | ⟨i,j⟩
    · exact Or.inl (fun v => by fin_cases v <;> simp [zero,i,j])
    · exact Or.inr (fun v => by fin_cases v <;> simp [zero,i,j,flip])
  have transport (rename : Nat → Nat) (colors : ∀ v : Fin 3, (e v).val=rename v.val) :
      homCount (matrix a) .nearClique arcs=homCount (matrix (!a)) .nearClique (arcs.map rename) := by
    apply RegionalPlanar.homCount_region p (by decide : 0<19) reg (f ∘ A.points) (g ∘ B.points)
      (D.injF.comp A.points.injective) (D.injG.comp B.points.injective)
      (fun z => (reindex f A.points z).trans (D.src z)) (fun z => (reindex g B.points z).trans (D.tgt z))
      _ _ (order a) (order (!a)) _ RegionalPlanar.drawing_nearClique _ rfl _
    intro i j x y eq k hk
    change c (A.points i) (A.points j)=d (B.points x) (B.points y) at eq
    have mapped : e (name a i j)=name (!a) x y := B.labels.injective <| (labels _).symm.trans
      ((A.cell _ _).symm.trans (eq.trans (B.cell _ _)))
    have small : k<3 := (show ∀ z ∈ arcs, z<3 by decide) _ hk
    let t : Fin 3 := ⟨k,small⟩
    rw [(rows a).2.2,(rows (!a)).2.2,←mapped,←show (e t).val=rename k from colors t]
    exact (Fin.val_inj (a:=name a i j) (b:=t)).trans (inj.eq_iff.symm.trans Fin.val_inj.symm)
  exfalso
  have clash : (if a then 3762 else 3654 : Nat) ≠ (if !a then 3762 else 3654) := by cases a <;> decide
  apply clash
  rcases cases3 with h|h
  · have eq := transport id h
    rw [List.map_id_fun] at eq
    exact (counts a).1.symm.trans (eq.trans (counts (!a)).1)
  · exact (counts a).1.symm.trans ((transport flip h).trans (counts (!a)).2)

end QGI.LargeOrderNineteen
