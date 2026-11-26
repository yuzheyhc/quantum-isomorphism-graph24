import DoubleEightColumnAdmissible
import DoubleEightInterfaceTransport
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.Sort

namespace QGI.DoubleEight.ColumnCoordinates
open ShoreCensus (V Coloring Homogeneous seed)
open FixedInterface (Compatible ConstantProduct Same product transpose)
open Finset
open scoped BigOperators

private theorem same_compatible {c l d m : Coloring} (cross : Same c d) (left : Same l m)
    (h : Compatible c l) : Compatible d m :=
  ⟨FixedInterface.transfer cross (FixedInterface.same_transpose cross) left h.1,
    FixedInterface.transfer left cross cross h.2⟩

private theorem move_constant {a b out : Coloring} (h : ConstantProduct a b out)
    (p q r : Equiv.Perm V) :
    ConstantProduct (fun i j => a (p i) (q j)) (fun i j => b (q i) (r j))
      (fun i j => out (p i) (r j)) := by
  intro u v i j x y eq
  have shift (i j : V) :
      product (fun i j => a (p i) (q j)) (fun i j => b (q i) (r j)) u v i j =
        product a b u v (p i) (r j) := by
    simp only [product,List.sum_ofFn]
    exact Equiv.sum_comp q (fun z => if a (p i) z = u ∧ b z (r j) = v then 1 else 0)
  exact (shift i j).trans ((h u v _ _ _ _ eq).trans (shift x y).symm)

private theorem move_compatible {c l : Coloring} (h : Compatible c l) (p q : Equiv.Perm V) :
    Compatible (fun i j => c (p i) (q j)) (fun i j => l (p i) (p j)) :=
  ⟨move_constant h.1 p q p,move_constant h.2 p p q⟩

private theorem unchanged (c : Coloring) : Same c c := fun _ _ _ _ => Iff.rfl

private def fromDigits (a b c d e f g h : Fin 4) : Nat :=
  16384 * a.val + 4096 * b.val + 1024 * c.val + 256 * d.val +
    64 * e.val + 16 * f.val + 4 * g.val + h.val

private theorem all_encodings : ∀ a b c d e f g h : Fin 4,
    let n := fromDigits a b c d e f g h
    n < 65536 ∧ ∀ i : V,
      ColumnEnum.letter n i.val = (#[a,b,c,d,e,f,g,h].getD i.val 0).val := by native_decide

private def encode (f : V → Fin 4) : Nat :=
  fromDigits (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)

private theorem encoding (f : V → Fin 4) :
    encode f < 65536 ∧ ∀ i : V, ColumnEnum.letter (encode f) i.val = (f i).val := by
  have h := all_encodings (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
  refine ⟨h.1,fun i => ?_⟩
  fin_cases i <;> first | exact h.2 0 | exact h.2 1 | exact h.2 2 | exact h.2 3
                        | exact h.2 4 | exact h.2 5 | exact h.2 6 | exact h.2 7

private theorem card_reindex (p : Equiv.Perm V) (P : V → Prop) [DecidablePred P] :
    ((univ : Finset V).filter (fun i => P (p i))).card = (univ.filter P).card := by
  simpa using Equiv.sum_comp p (fun i => (if P i then 1 else 0 : Nat))

/-- Choose a point labeling of the left shore, an injective renaming of the
cross colors and a sorting permutation of the right points. The resulting
eight base-four columns occur in the actual executable search domain. -/
theorem coordinates {c l : Coloring} (hl : Homogeneous l) (hc : Compatible c l) {ds : List Nat}
    (hds : ds ∈ ColumnProfiles.profiles) (hp : ColumnProfiles.Presentation c ds) :
    ∃ (a : Fin 21) (cols : List Nat) (q : ColumnEnum.Signature),
      ColumnEnum.Admissible (UniformInput.shores.getD a.val #[]) ds q cols ∧
      InterfaceTransport.CrossIso c (fun i j => ColumnEnum.letter (cols.getD j.val 0) i.val) := by
  classical
  obtain ⟨name,index,inject,names,counts⟩ := hp
  obtain ⟨a,p,hp⟩ := ShoreCensus.every_shore l hl
  let dense : Coloring := fun i j => (index i j).val
  have same : Same c dense := by
    intro i j x y
    simp only [← names i j,← names x y,inject.eq_iff,dense,Fin.val_inj]
  have left : Same (fun i j => l (p i) (p j)) (seed a) := fun i j x y => (hp i j x y).symm
  have check : ColumnProfiles.profiles.all (fun ps => decide (ps.length ≤ 4)) = true := by decide
  have maxRank : ds.length ≤ 4 := of_decide_eq_true (List.all_eq_true.mp check _ hds)
  let digits := fun (j i : V) => (⟨(index (p i) j).val,lt_of_lt_of_le (index _ _).isLt maxRank⟩ : Fin 4)
  let code := fun j => encode (digits j)
  let perm := Tuple.sort code
  let cols := List.ofFn (code ∘ perm)
  let d : Coloring := fun i j => dense (p i) (perm j)
  have len : cols.length = 8 := List.length_ofFn
  have ordered : cols.Pairwise (· ≤ ·) := (Tuple.monotone_sort code).ofFn_sorted
  have nth (j : V) : cols.getD j.val 0 = code (perm j) := by
    have hj : j.val < cols.length := by rw [len]; exact j.isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp only [Option.getD_some, cols,List.getElem_ofFn,Function.comp_apply]
  have bounded : ∀ w ∈ cols, w < 65536 := by
    intro w hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact (encoding _).1
  have digitsOK (i j : V) : ColumnEnum.letter (cols.getD j.val 0) i.val = d i j := by
    rw [nth]
    exact (encoding _).2 i
  have dc : Compatible d (seed a) :=
    same_compatible (unchanged d) left (move_compatible (same_compatible same (unchanged l) hc) p perm)
  have rows (s : Fin ds.length) (i : V) :
      ((univ : Finset V).filter (fun j => d i j = s.val)).card = ds.get s := by
    change ((univ : Finset V).filter (fun j => (index (p i) (perm j)).val = s.val)).card = _
    simp only [Fin.val_inj]
    exact (card_reindex perm (fun y => index (p i) y = s)).trans ((counts s).1 (p i))
  have columns (s : Fin ds.length) (j : V) :
      ((univ : Finset V).filter (fun i => d i j = s.val)).card = ds.get s := by
    change ((univ : Finset V).filter (fun i => (index (p i) (perm j)).val = s.val)).card = _
    simp only [Fin.val_inj]
    exact (card_reindex p (fun x => index x (perm j) = s)).trans ((counts s).2 (perm j))
  obtain ⟨q,hq⟩ := ColumnBridge.admissible a ds cols d hds len ordered bounded digitsOK
    (fun i j => (index (p i) (perm j)).isLt) rows columns dc
  refine ⟨a,cols,q,hq,p.symm,perm.symm,fun i j x y => ?_⟩
  simpa only [digitsOK,d,Equiv.apply_symm_apply] using same i j x y

end QGI.DoubleEight.ColumnCoordinates
