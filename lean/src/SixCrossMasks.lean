import SixShoreModels
import SixSixCatalog

namespace QGI.SixCross
open SixShoreAtlas (Key cell)
open ZivAvSix (S M part degree Cyclic cycleEdge)

def countIn (m : M) (s : Finset S) (i : S) (v : Nat) :=
  (s.filter fun x => m i x=v).card

/-- The view of one cross color from a vertex on the opposite shore.
Double-counting a two-step path gives the divisibility test. -/
def Basic (a : Key) (s : Finset S) : Prop :=
  2≤s.card ∧ ∀ i∈s, ∀ j : S, ∀ t : S,
    (j∈s → countIn (cell a) s i (cell a 0 t)=countIn (cell a) s j (cell a 0 t)) ∧
    countIn (cell a) Finset.univ 0 (cell a 0 t) ∣ s.card*countIn (cell a) s i (cell a 0 t)
private instance (a s) : Decidable (Basic a s) := by unfold Basic; infer_instance

private def basicSets := Vector.ofFn fun a : Key => Finset.univ.filter (Basic a)
def possible := Vector.ofFn fun a : Key =>
  let sets := basicSets.get a
  sets.filter fun s => ∀ x : S, x∉s → ∃ t∈sets, x∈t ∧ Disjoint t s

theorem admit (a : Key) {s : Finset S} (ok : Basic a s)
    (other : ∀ x : S, x∉s → ∃ t : Finset S, Basic a t ∧ x∈t ∧ Disjoint t s) :
    s∈possible.get a := by
  simpa [possible,basicSets,Vector.get] using And.intro ok other

def width (a : Key) : Nat := ![6,2,3,3,2,2,2,2] a
private def cycleRow (a : Key) (i : S) : S :=
  if a=4 then ![0,4,3,1,2,5] i else if a=7 then ![0,3,4,1,2,5] i else i
def hasCycle (a : Key) := a=4 ∨ a=6 ∨ a=7
instance (a) : Decidable (hasCycle a) := by unfold hasCycle; infer_instance
theorem cycle_of {a : Key} (h : hasCycle a) : Cyclic (cell a) := by
  have test : ∀ a : Key, hasCycle a →
      (∀ i j, cycleRow a i=cycleRow a j → i=j) ∧ ∀ i j x y,
      cell a (cycleRow a i) (cycleRow a j)=cell a (cycleRow a x) (cycleRow a y) →
        cycleEdge i j=cycleEdge x y := by native_decide
  obtain ⟨inj,rows⟩ := test a h
  exact ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp inj),rows⟩

private instance (m : M) (i j : S) : Decidable (part m i j) := by unfold part; infer_instance

theorem columns : ∀ a : Key, ¬hasCycle a → ∀ s∈possible.get a, ∀ i j,
    part (cell a) i j → i∈s → j∈s := by native_decide

theorem alternatives : ∀ a : Key, ¬hasCycle a → ∀ s∈possible.get a, ∀ t∈possible.get a,
    Disjoint s t → s.card=width a ∨ t.card=width a := by native_decide

theorem singlePart : ∀ a : Key, ¬hasCycle a → ∀ s∈possible.get a,
    s.card=width a → ∀ i∈s, ∀ j∈s, part (cell a) i j := by native_decide

theorem sizes : ∀ a : Key, ¬hasCycle a → ∀ s∈possible.get a, s.card=width a →
    s≠Finset.univ → width a=2 ∨ width a=3 := by native_decide

private def anchor (a : Key) (k : Nat) : S := if k=2 ∧ (a=1 ∨ a=4) then 2 else 0

theorem anchors (a : Key) (k : Nat) (h : k=2 ∨ k=3) : ∃ u v : S,
    ∀ s∈possible.get a, s.card=k → ∀ i j, cell a u i=cell a u j → cell a v i=cell a v j → i∈s → j∈s := by
  have test : ∀ a : Key, ∀ k : Fin 4, (k.val=2 ∨ k.val=3) →
      ∀ s∈possible.get a, s.card=k.val → ∀ i j, cell a 0 i=cell a 0 j →
        cell a (anchor a k.val) i=cell a (anchor a k.val) j → i∈s → j∈s := by native_decide
  exact ⟨0,anchor a k,test a ⟨k,by omega⟩ h⟩

end QGI.SixCross
