import data.ZivAvSixPairs
import SmallUnionRealization
import SixTenCoordinates

set_option maxRecDepth 16000
namespace QGI.ZivAvSix
abbrev S := Fin 6
abbrev M := S → S → Nat
abbrev Index := Fin rows.size
def raw (k : Index) (a b : Nat) (i j : S) : Nat :=
  (rows[k].2.2.1 >>> (8 * (12 * (6*a+i.val) + 6*b+j.val))) % 256
def same (A B : M) := ∀ i j x y, A i j=A x y ↔ B i j=B x y
def degree (B : M) (i j : S) := ∑ k, if B i k = B i j then 1 else (0:Nat)
def part (B : M) (i j : S) : Prop := i=j ∨ ∀ k, i≠k → degree B i j ≤ degree B i k
def cycleEdge (i j : S) : Bool := decide (i+1=j ∨ j+1=i)
def Thin (T : M) := ∃ i j, ∀ z, T i z=T i j → z=j
def Cyclic (N : M) := ∃ e : Equiv.Perm S, ∀ i j x y,
  N (e i) (e j)=N (e x) (e y) → cycleEdge i j=cycleEdge x y
def Constant (T : M) := ∀ i j x y, T i j=T x y
def Columns (N T : M) := ∀ x z i, part N z x → T i z=T i x
def Marked (B N T : M) := ∃ h j₀ a b : S,
  (∀ i j y, B a i=B a j → B b i=B b j → T i y=T h j₀ → T i y=T j y) ∧
  ∀ x, ∃ i, T i x=T h j₀ ∧ ∀ z, T i z=T i x → part N z x
def Shape (B N T : M) := Thin T ∨ Cyclic N ∨ (Columns N T ∧ (Constant T ∨ Marked B N T))

private def digit (k : Index) (i : Nat) : S := ⟨((rows[k].2.2.2.2 >>> (3*i)) % 8) % 6,by omega⟩
private def cyc (k : Index) (i : S) := digit k i.val
private def check (k : Index) : Bool := 
  let B := raw k 0 0
  let N := raw k 1 1
  let T := raw k 0 1
  let w := digit k
  match rows[k].2.2.2.1 with
  | 0 => decide (∀ i j, T i j=T 0 0)
  | 1 => decide (∀ z, T 0 z=T 0 (w 0) → z=w 0)
  | 2 => decide ((∀ i j, cyc k i=cyc k j → i=j) ∧ ∀ i j x y,
      N (cyc k i) (cyc k j)=N (cyc k x) (cyc k y) → cycleEdge i j=cycleEdge x y)
  | 3 => decide ((∀ x z i, (z=x ∨ ∀ j, z≠j → degree N z x ≤ degree N z j) → T i z=T i x) ∧
      (∀ i j y, B (w 1) i=B (w 1) j → B (w 2) i=B (w 2) j →
        T i y=T 0 (w 0) → T i y=T j y) ∧
      ∀ x, ∃ i, T i x=T 0 (w 0) ∧ ∀ z, T i z=T i x →
        (z=x ∨ ∀ j, z≠j → degree N z x ≤ degree N z j))
  | _ => false

set_option maxRecDepth 16000 in
private theorem checked : ∀ k : Index, check k = true := by native_decide

theorem shape (k : Index) : Shape (raw k 0 0) (raw k 1 1) (raw k 0 1) := by
  have h := checked k
  match eq : rows[k].2.2.2.1 with
  | 0 =>
    have all : ∀ i j, raw k 0 1 i j=raw k 0 1 0 0 := by simpa only [check,eq,decide_eq_true_eq] using h
    have c : Constant (raw k 0 1) := fun i j x y => (all i j).trans (all x y).symm
    exact Or.inr (Or.inr ⟨fun _ _ _ _ => c _ _ _ _,Or.inl c⟩)
  | 1 =>
    exact Or.inl ⟨0,digit k 0,by simpa only [check,eq,decide_eq_true_eq] using h⟩
  | 2 =>
    simp only [check,eq,Id.run,decide_eq_true_eq] at h
    exact Or.inr (Or.inl ⟨Equiv.ofBijective (cyc k) (Finite.injective_iff_bijective.mp h.1),h.2⟩)
  | 3 =>
    simp only [check,eq,Id.run,decide_eq_true_eq] at h
    exact Or.inr (Or.inr ⟨h.1,Or.inr ⟨0,digit k 0,digit k 1,digit k 2,h.2⟩⟩)
  | k'+4 => simp only [check,eq,Bool.false_eq_true] at h

structure Matches (B N T B' N' T' : M) (e f : Equiv.Perm S) : Prop where
  outer : same (fun i j => B (e i) (e j)) B'
  inner : same (fun i j => N (f i) (f j)) N'
  cross : same (fun i j => T (e i) (f j)) T'

theorem transport {B N T B' N' T' : M} {e f} (m : Matches B N T B' N' T' e f)
    (sh : Shape B' N' T') : Shape B N T := by
  have deg (i j) : degree N (f i) (f j)=degree N' i j := by
    rw [degree,←Equiv.sum_comp f (fun z => if N (f i) z=N (f i) (f j) then 1 else (0:Nat))]
    exact Finset.sum_congr rfl fun z _ => if_congr (m.inner i z i j) rfl rfl
  have partEq (i j) : part N (f i) (f j) ↔ part N' i j := by
    unfold part
    rw [f.injective.eq_iff]
    apply or_congr_right
    constructor
    · intro h k hk; simpa only [deg] using h (f k) (f.injective.ne hk)
    · intro h z
      obtain ⟨k,rfl⟩ := f.surjective z
      simpa only [f.injective.ne_iff,deg] using h k
  rcases sh with ⟨i,j,h⟩ | ⟨q,h⟩ | ⟨cols,other⟩
  · refine Or.inl ⟨e i,f j,fun z eq => ?_⟩
    obtain ⟨z,rfl⟩ := f.surjective z
    exact congrArg f (h z ((m.cross _ _ _ _).mp eq))
  · exact Or.inr (Or.inl ⟨q.trans f,fun i j x y eq => h i j x y ((m.inner _ _ _ _).mp eq)⟩)
  · right; right
    constructor
    · intro x z i hit
      obtain ⟨x,rfl⟩ := f.surjective x
      obtain ⟨z,rfl⟩ := f.surjective z
      obtain ⟨i,rfl⟩ := e.surjective i
      exact (m.cross _ _ _ _).mpr (cols x z i ((partEq _ _).mp hit))
    · rcases other with c | ⟨h,j₀,a,b,row,col⟩
      · left; intro i j x y
        obtain ⟨i,rfl⟩ := e.surjective i
        obtain ⟨j,rfl⟩ := f.surjective j
        obtain ⟨x,rfl⟩ := e.surjective x
        obtain ⟨y,rfl⟩ := f.surjective y
        exact (m.cross _ _ _ _).mpr (c _ _ _ _)
      · right
        refine ⟨e h,f j₀,e a,e b,?_,?_⟩
        · intro i j y
          obtain ⟨i,rfl⟩ := e.surjective i
          obtain ⟨j,rfl⟩ := e.surjective j
          obtain ⟨y,rfl⟩ := f.surjective y
          exact fun A D t => (m.cross _ _ _ _).mpr (row i j y ((m.outer _ _ _ _).mp A)
            ((m.outer _ _ _ _).mp D) ((m.cross _ _ _ _).mp t))
        · intro x
          obtain ⟨x,rfl⟩ := f.surjective x
          obtain ⟨i,hi,all⟩ := col x
          refine ⟨e i,(m.cross _ _ _ _).mpr hi,fun z eq => ?_⟩
          obtain ⟨z,rfl⟩ := f.surjective z
          exact (partEq _ _).mpr (all z ((m.cross _ _ _ _).mp eq))

end QGI.ZivAvSix
