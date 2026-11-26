import Mathlib.Tactic
import Mathlib.Data.Fintype.Perm

namespace QGI.TenMatchedSigns
abbrev Q := Fin 5
abbrev Row := Fin 16
abbrev Table := Q → Q → Bool
def digit (r : Row) (i j : Q) := r.val.testBit (if j < i then j.val else j.val-1)
def agree (a : Table) (i j : Q) := (Finset.univ.filter fun k => k≠i ∧ k≠j ∧ a i k=a j k).card
def cycle (k : Nat) (i j : Q) := decide (k≠3 ∧ (i+1=j ∨ j+1=i))
def Normal (a : Table) (k : Nat) := ∃ f : Equiv.Perm Q, ∃ b : Bool, ∀ i j, i≠j → a i j=xor b (cycle k (f i) (f j))
instance (a : Table) (k : Nat) : Decidable (Normal a k) := by unfold Normal; infer_instance

def make (a b c d e : Row) : Table :=
  fun i j => digit (![a,b,c,d,e] i) i j
private theorem enc : ∀ (i : Q) (f : Q → Bool), ∃ r : Row, ∀ j, i≠j → digit r i j=f j := by native_decide
private def rowAgree (i j : Q) (a b : Row) := (Finset.univ.filter fun k => k≠i ∧ k≠j ∧ digit a i k=digit b j k).card

private theorem checked : ∀ a b : Row, let k := rowAgree 0 1 a b
    ∀ c : Row, rowAgree 0 2 a c=k → rowAgree 1 2 b c=k →
    ∀ d : Row, rowAgree 0 3 a d=k → rowAgree 1 3 b d=k → rowAgree 2 3 c d=k →
    ∀ e : Row, rowAgree 0 4 a e=k → rowAgree 1 4 b e=k → rowAgree 2 4 c e=k → rowAgree 3 4 d e=k →
    (∀ i j : Q, i≠j → agree (Function.swap (make a b c d e)) i j=agree (Function.swap (make a b c d e)) 0 1) →
    Normal (make a b c d e) k := by native_decide

theorem canonical (a : Table) (row : ∀ i j, i≠j → agree a i j=agree a 0 1)
    (col : ∀ i j, i≠j → agree (Function.swap a) i j=agree (Function.swap a) 0 1) : Normal a (agree a 0 1) := by
  choose r hr using fun i => enc i (a i)
  let m := make (r 0) (r 1) (r 2) (r 3) (r 4)
  have read (i j : Q) (ne : i≠j) : m i j=a i j := by fin_cases i <;> exact hr _ j ne
  have gram {f g : Table} (same : ∀ i j, i≠j → f i j=g i j) (i j : Q) : agree f i j=agree g i j := by
    unfold agree; congr 1; ext k; simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases h : k=i
    · simp [h]
    by_cases e : k=j
    · simp [e]
    simp only [h,e,not_false_eq_true,true_and,same i k (Ne.symm h),same j k (Ne.symm e)]
  have localEq (i j : Q) : rowAgree i j (r i) (r j)=agree a i j := gram (f:=fun i j => digit (r i) i j) hr i j
  have kc := checked (r 0) (r 1)
  dsimp only at kc
  have same (i j : Q) (neq : i≠j) : rowAgree i j (r i) (r j)=rowAgree 0 1 (r 0) (r 1) := by rw [localEq,localEq,row _ _ neq]
  have cols (i j : Q) (neq : i≠j) : agree (Function.swap m) i j=agree (Function.swap m) 0 1 := by
    have sw : ∀ x y : Q, x≠y → Function.swap m x y=Function.swap a x y := fun x y h => read y x (Ne.symm h)
    rw [gram sw,gram sw,col _ _ neq]
  obtain ⟨f,b,h⟩ := kc (r 2) (same _ _ (by decide)) (same _ _ (by decide)) (r 3)
    (same _ _ (by decide)) (same _ _ (by decide)) (same _ _ (by decide)) (r 4) (same _ _ (by decide))
    (same _ _ (by decide)) (same _ _ (by decide)) (same _ _ (by decide)) cols
  exact ⟨f,b,fun i j ne => (read i j ne).symm.trans (by rw [←localEq 0 1]; exact h i j ne)⟩

theorem align (a b : Table) (k : Nat) (na : Normal a k) (nb : Normal b k) :
    ∃ f : Equiv.Perm Q, ∃ flip : Bool, ∀ i j, i≠j → b (f i) (f j)=xor flip (a i j) := by
  obtain ⟨x,s,hs⟩ := na
  obtain ⟨y,t,ht⟩ := nb
  let f := x.trans y.symm
  refine ⟨f,xor t s,fun i j ne => ?_⟩
  rw [ht _ _ (f.injective.ne ne),hs _ _ ne]
  simp only [f,Equiv.trans_apply,Equiv.apply_symm_apply]
  cases s <;> cases t <;> simp

end QGI.TenMatchedSigns
