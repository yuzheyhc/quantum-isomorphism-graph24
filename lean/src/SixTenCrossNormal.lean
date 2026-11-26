import SixTenCrossCertificate
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Fin

set_option maxHeartbeats 2000000

namespace QGI.SixTen.Cross

open scoped BigOperators

def rowGram (B : Matrix) (i h : L) : Nat :=
  (Finset.univ.filter fun j => B i j = true ∧ B h j = true).card

def colGram (B : Matrix) (j t : R) : Nat :=
  (Finset.univ.filter fun i => B i j = true ∧ B i t = true).card

def encode : {n : Nat} → (Fin n → Bool) → Nat
  | 0,_ => 0
  | n+1,f => Nat.bit (f 0) (encode (fun i : Fin n => f i.succ))

theorem encode_lt {n : Nat} (f : Fin n → Bool) : encode f < 2^n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
    have h := ih (fun i => f i.succ)
    change Nat.bit (f 0) _ < _
    cases f 0 <;> simp only [Nat.bit_false,Nat.bit_true,pow_succ] <;> omega

theorem decode {n : Nat} (f : Fin n → Bool) (i : Fin n) : (encode f).testBit i.val = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Nat.testBit_bit_zero _ _
    · exact (Nat.testBit_bit_succ _ _ _).trans (ih (fun j => f j.succ) j)

private theorem countP_sum {α : Type} (l : List α) (f : α → Bool) :
    l.countP f = (l.map fun x => if f x then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [List.countP_cons,h,ih,Nat.add_comm]

theorem count_ofFn {α : Type} {n : Nat} (v : Fin n → α) (f : α → Bool) :
    (List.ofFn v).countP f = (Finset.univ.filter fun i => f (v i) = true).card := by
  rw [countP_sum, List.map_ofFn,List.sum_ofFn]
  simp [Function.comp_apply]

theorem count_fin {n : Nat} (f : Fin n → Bool) :
    (List.finRange n).countP f = (Finset.univ.filter fun i => f i = true).card := by
  rw [←List.ofFn_id]
  exact count_ofFn _ _

theorem card_relabel {n : Nat} (q : Equiv.Perm (Fin n)) (f : Fin n → Prop) [DecidablePred f] :
    (Finset.univ.filter fun i => f (q i)).card = (Finset.univ.filter f).card := by
  simpa using Equiv.sum_comp q (fun j => (if f j then 1 else 0 : Nat))

theorem normal (B : Matrix)
    (rows : ∀ i, (Finset.univ.filter (fun j => B i j = true)).card = 5)
    (cols : ∀ j, (Finset.univ.filter (fun i => B i j = true)).card = 3)
    (lh : ∀ (i u : L) (k : Nat), (Finset.univ.filter (fun h => rowGram B i h = k)).card =
      (Finset.univ.filter (fun h => rowGram B u h = k)).card)
    (rh : ∀ (j v : R) (k : Nat), (Finset.univ.filter (fun t => colGram B j t = k)).card =
      (Finset.univ.filter (fun t => colGram B v t = k)).card) :
    ∃ (p : Equiv.Perm L) (q : Equiv.Perm R),
      (∀ i j, B i j = splitModel (p i) (q j)) ∨ (∀ i j, B i j = design (p i) (q j)) := by
  let r := fun j : R => encode (fun i => B i j)
  let e := Tuple.sort r
  let v := fun j : R => r (e j)
  let cs := List.ofFn v
  have digit (i : L) (j : R) : bit (v j) i = B i (e j) := decode _ _
  have lookup (j : R) : cs.getD j.val 0 = v j := by
    have hj : j.val < cs.length := by simpa only [cs,List.length_ofFn] using j.isLt
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
    simp only [Option.getD_some,cs,List.getElem_ofFn]
  have rowD (i : L) : rowCount cs i = 5 := by
    change (List.ofFn v).countP _ = _
    rw [count_ofFn]; simp only [digit]
    exact (card_relabel e (fun j => B i j = true)).trans (rows i)
  have regular : cs ∈ regularMatrices := by
    apply regular_complete (by simp [cs]) _ _ rowD (List.pairwise_ofFn.mpr (fun {_ _} h => Tuple.monotone_sort r h.le))
    · intro c hc; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
      exact encode_lt _
    · intro c hc; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
      change (List.finRange 6).countP _ = _
      rw [count_fin]
      simpa only [digit] using cols (e j)
  have gl (i h : L) : leftOverlap cs i h = rowGram B i h := by
    unfold leftOverlap cs
    rw [count_ofFn]
    simpa only [digit,Bool.and_eq_true] using card_relabel e (fun j => B i j = true ∧ B h j = true)
  have gr (i j : R) : rightOverlap (v i) (v j) = colGram B (e i) (e j) := by
    simp only [rightOverlap,count_fin,digit,Bool.and_eq_true,colGram]
  have hl (i : L) : leftHist cs i = leftHist cs 0 := by
    unfold leftHist
    apply congrArg List.ofFn
    funext k
    simp only [count_fin,gl,beq_iff_eq]
    exact lh _ _ _
  have hr (i : R) : rightHist cs i = rightHist cs 0 := by
    unfold rightHist
    apply congrArg List.ofFn
    funext k
    simp only [lookup,cs,count_ofFn,gr,beq_iff_eq]
    exact (card_relabel e _).trans ((rh _ _ _).trans (card_relabel e _).symm)
  have uniform : uniformHist cs = true := by simp [uniformHist,hl,hr]
  obtain ⟨p,q,st⟩ := classify regular uniform
  have eq (i j) : asMatrix cs i j = B i (e j) := by rw [asMatrix,lookup,digit]
  refine ⟨p,e.symm.trans q,?_⟩
  rcases st with h | h
  · left; intro i j; simpa only [eq,Equiv.apply_symm_apply] using h i (e.symm j)
  · right; intro i j; simpa only [eq,Equiv.apply_symm_apply] using h i (e.symm j)

end QGI.SixTen.Cross