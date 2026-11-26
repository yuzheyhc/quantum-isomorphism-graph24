import RegionalSixTenDesign
import SixTenDesignBridge
import SmallUnionRealization

noncomputable section
namespace QGI.Coherent.RegionalSixTen
open SixTenCoordinates SmallUnion
open QGI.SixTen.Cross (design rowGram colGram)
open private same_name incidence countBlock sample rowDiagonal renumber from SixTenDesignBridge
open private diagonalOnly diagonalValue from SixTenDesignGraph

private theorem indicator {c : Coloring} {u : Nat} {X : Type} (L : Shore c u X) (s : Nat) :
    Block L L L L (fun i j => decide (c (atPoint L i) (atPoint L j)=s))
      (fun i j => decide (c (atPoint L i) (atPoint L j)=s)) :=
  fun ⦃_ _ _ _⦄ h => congrArg (fun v => decide (v=s)) h

private theorem orientation {d : Coloring} (law : Laws d d) {r : Nat}
    (R : Shore d r B) (s : Nat) :
    let mask := fun i j : B => decide (d (atPoint R i) (atPoint R j)=s)
    (∀ i j, mask i j=mask j i) ∨ (∀ i j, mask i j=true → mask j i=false) := by
  classical
  dsimp only
  by_cases hit : ∃ u v : B, d (atPoint R u) (atPoint R v)=s ∧ d (atPoint R v) (atPoint R u)=s
  · obtain ⟨u,v,h,h'⟩ := hit
    left
    intro i j
    apply decide_eq_decide.mpr
    exact ⟨fun eq => (law.rev (eq.trans h.symm)).trans h',fun eq => (law.rev (eq.trans h'.symm)).trans h⟩
  · right
    intro i j h
    apply decide_eq_false
    exact fun rev => hit ⟨i,j,of_decide_eq_true h,rev⟩

private theorem canonical {c d : Coloring} (hd : Configuration d) (law : Laws d d) (commonLaw : Laws c d)
    {l r : Nat} (f : Frame c l r) (g : Frame d l r) (v w : Nat)
    (twoG : ∀ i j, cross f i j=v ∨ cross f i j=w) (twoH : ∀ i j, cross g i j=v ∨ cross g i j=w)
    (src : ∀ i j, basic f v i j=design i j) (tgt : ∀ i j, basic g v i j=design i j) :
    ∃ e : Equiv.Perm V, ∀ i j, c i j=d (e i) (e j) := by
  let L := g.leftShore
  let R := g.rightShore
  have dsg := incidence g g tgt tgt
  have common := incidence f g src tgt
  have names {i j x y} (eq : design i j=design x y) : cross g i j=cross g x y :=
    same_name (twoH i j) (twoH x y) ((tgt i j).trans (eq.trans (tgt x y).symm))
  have gramL : Block f.leftShore L f.leftShore L (rowGram design) (rowGram design) :=
    Block.gram commonLaw common
  have gramR : Block f.rightShore R f.rightShore R (colGram design) (colGram design) :=
    Block.gram commonLaw (Block.flip commonLaw common)
  have leftRow (i j y : A) (jy : j≠i) (yy : y≠i) :
      d (atPoint L i) (atPoint L j)=d (atPoint L i) (atPoint L y) := by
    let s := d (atPoint L i) (atPoint L j)
    let mask := fun a b : A => decide (d (atPoint L a) (atPoint L b)=s)
    have off : s≠l := by
      intro eq
      have pt := hd.diagonal _ _ _ (eq.trans (L i).property.symm)
      exact jy (L.injective (Subtype.ext pt.symm))
    have diag (a : A) : mask a a=false := decide_eq_false (fun eq => off (eq.symm.trans (L a).property))
    have hit := QGI.SixTen.Cross.left_color_row mask diag (fun i j k eq =>
      countBlock law (indicator L s) dsg (names eq)) i j y jy yy
    exact (of_decide_eq_true (show mask i y=true from hit.symm.trans (decide_eq_true rfl))).symm
  have rightRow (i j x y : B) (share : colGram design i j=colGram design x y) :
      d (atPoint R i) (atPoint R j)=d (atPoint R x) (atPoint R y) := by
    by_cases ij : i=j
    · subst j
      obtain rfl := (diagonalOnly x y).mp (share.symm.trans (diagonalValue i))
      exact (R i).property.trans (R x).property.symm
    let s := d (atPoint R i) (atPoint R j)
    let mask := fun a b : B => decide (d (atPoint R a) (atPoint R b)=s)
    have off : s≠r := by
      intro eq
      exact ij (R.injective (Subtype.ext (hd.diagonal _ _ _ (eq.trans (R i).property.symm))))
    have diag (a : B) : mask a a=false := decide_eq_false (fun eq => off (eq.symm.trans (R a).property))
    have gram : Block R R R R (colGram design) (colGram design) := Block.gram law (Block.flip law dsg)
    let sel := fun k (j w : B) => mask j w && decide (colGram design j w=k)
    have selLaw (k : Nat) : Block R R R R (sel k) (sel k) :=
      Block.map₂ (indicator R s) gram (fun b n => b && decide (n=k))
    have regular (k : Nat) (j x : B) : QGI.SixTen.Cross.selectedDegree mask k j=QGI.SixTen.Cross.selectedDegree mask k x := by
      simpa only [sel,Bool.and_eq_true,decide_eq_true_eq,QGI.SixTen.Cross.selectedDegree] using
        Block.degree_eq law (selLaw k) j x
    have mixed (k : Nat) (i x : A) (j : B) (eq : design i j=design x j) :
        QGI.SixTen.Cross.mixedDegree mask k i j=QGI.SixTen.Cross.mixedDegree mask k x j := by
      simpa only [sel,Bool.and_eq_true,decide_eq_true_eq,QGI.SixTen.Cross.mixedDegree] using
        countBlock law dsg (Block.flip law (selLaw k)) (names eq)
    rcases orientation law R s with symm | disjoint
    · have h := QGI.SixTen.Cross.right_graph mask symm diag regular mixed i j x y share
      exact (of_decide_eq_true (show mask x y=true from h.symm.trans (decide_eq_true rfl))).symm
    · have h := QGI.SixTen.Cross.directed_empty mask disjoint regular mixed i j
      exact False.elim (Bool.noConfusion ((show mask i j=true from decide_eq_true rfl).symm.trans h))
  have ll (i j : A) : c (f.e (.inl i)) (f.e (.inl j))=d (g.e (.inl i)) (g.e (.inl j)) := by
    obtain ⟨y,hy⟩ := sample commonLaw f.leftShore L f.leftShore L i j
    have z := gramL hy
    by_cases eq : j=i
    · subst j; simpa only [(rowDiagonal i y).mp z.symm] using hy
    · have ny : y≠i := by intro h; rw [h] at z; exact eq ((rowDiagonal i j).mp z)
      exact hy.trans (leftRow i y j ny eq)
  have rr (i j : B) : c (f.e (.inr i)) (f.e (.inr j))=d (g.e (.inr i)) (g.e (.inr j)) := by
    obtain ⟨y,hy⟩ := sample commonLaw f.rightShore R f.rightShore R i j
    exact hy.trans (rightRow i y i j (gramR hy).symm)
  have lr (i : A) (j : B) : c (f.e (.inl i)) (f.e (.inr j))=d (g.e (.inl i)) (g.e (.inr j)) :=
    same_name (twoG i j) (twoH i j) ((src i j).trans (tgt i j).symm)
  refine ⟨f.e.symm.trans g.e,?_⟩
  intro x y
  obtain ⟨x,rfl⟩ := f.e.surjective x
  obtain ⟨y,rfl⟩ := f.e.surjective y
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
  cases x with
  | inl x => cases y with | inl y => exact ll x y | inr y => exact lr x y
  | inr x => cases y with | inl y => exact commonLaw.rev (lr y x) | inr y => exact rr x y

theorem design_named {c d : Coloring} (hd : Configuration d) (law : Laws d d) (commonLaw : Laws c d)
    {l r : Nat} (f : Frame c l r) (g : Frame d l r) (v w : Nat)
    (twoG : ∀ i j, cross f i j=v ∨ cross f i j=w) (twoH : ∀ i j, cross g i j=v ∨ cross g i j=w)
    (a a' : Equiv.Perm A) (b b' : Equiv.Perm B)
    (src : ∀ i j, basic f v i j=design (a i) (b j))
    (tgt : ∀ i j, basic g v i j=design (a' i) (b' j)) :
    ∃ e : Equiv.Perm V, ∀ i j, c i j=d (e i) (e j) := by
  apply canonical hd law commonLaw (renumber f a b) (renumber g a' b') v w
  · exact fun i j => twoG (a.symm i) (b.symm j)
  · exact fun i j => twoH (a'.symm i) (b'.symm j)
  · intro i j; change basic f v (a.symm i) (b.symm j)=_
    simpa only [Equiv.apply_symm_apply] using src (a.symm i) (b.symm j)
  · intro i j; change basic g v (a'.symm i) (b'.symm j)=_
    simpa only [Equiv.apply_symm_apply] using tgt (a'.symm i) (b'.symm j)

end QGI.Coherent.RegionalSixTen
