import ZivAvCoreQuantum
import FourTwelveCycle
import SplitRectangleGluing

namespace QGI.Coherent.SixEightCatalog
open QGI.ZivAv
open FourTwelveCycle (edge)
abbrev Six := Fin 6
abbrev Eight := Fin 8

def left (i : Six) : Vertex := ⟨i.val,by omega⟩
def right (j : Eight) : Vertex := ⟨6+j.val,by omega⟩
def diagSize (a : Index) (i : Vertex) := (Finset.univ.filter (fun j => name a j j=name a i i)).card
def M (a : Index) (i : Six) (j : Eight) := name a (left i) (right j)
def A (a : Index) (i j : Six) := name a (left i) (left j)
def B (a : Index) (i j : Eight) := name a (right i) (right j)

attribute [local irreducible] raw color cores14
theorem coordinates : ∀ a : Index, (∃ i, diagSize a i=6) → (∃ i, diagSize a i=8) →
    (∀ i, diagSize a (left i)=6) ∧ ∀ j, diagSize a (right j)=8 := by native_decide

def edgeIndex : Six → Six := ![0,2,4,5,3,1]
def slots (a : Index) : Eight → Eight :=
  if a.val=138 ∨ a.val=170 then ![0,1,2,5,3,7,4,6]
  else if a.val=167 ∨ a.val=315 then ![0,1,2,5,3,6,4,7] else id

def number (j : Fin 4 × Fin 2) : Eight := ⟨2*j.1.val+j.2.val,by omega⟩
def flag (a : Index) := M a 0 0
def other (a : Index) := M a 1 0
def Tetra (a : Index) : Prop := flag a≠other a ∧
  ∀ (i : Six) (j : Fin 4) (t : Fin 2), M a (edgeIndex i) (slots a (number (j,t)))=if j∈edge i then flag a else other a

def cube (a : Index) := a.val=168 ∨ a.val=316
instance (a : Index) : Decidable (cube a) := by unfold cube; infer_instance
instance (a : Index) : Decidable (Tetra a) := by unfold Tetra; infer_instance
private instance (a : Index) : Decidable (SplitRectangle.Twins (fun i j => (M a i j).val)) := by
  unfold SplitRectangle.Twins; infer_instance

theorem geometry : ∀ a : Index, diagSize a (left 0)=6 → diagSize a (right 0)=8 →
    SplitRectangle.Twins (fun i j => (M a i j).val) ∨ Tetra a ∨ cube a := by native_decide

theorem edge_perm : Function.Bijective edgeIndex := by
  exact Finite.injective_iff_bijective.mp (by decide : Function.Injective edgeIndex)
theorem slot_perm (a : Index) : Function.Bijective (fun j => slots a (number j)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,by decide⟩
  revert a; native_decide

theorem cube_shore : ∀ a : Index, cube a → ∀ i j : Eight, (Finset.univ.filter (fun b => B a i b=B a i j)).card≤3 := by native_decide
theorem nonuniform_columns : ∀ a : Index, diagSize a (left 0)=6 → diagSize a (right 0)=8 →
    (∀ i j, M a i j=M a 0 0) ∨ (∀ j i, (Finset.univ.filter (fun b => M a b j=M a i j)).card≤3) := by native_decide

private def columnFits (a : Index) (f : Six → Six) (j b : Eight) : Bool :=
  decide (∀ i, M a (f i) b=M a i j)
private def liftCol (a : Index) (f : Six → Six) (j : Eight) : Eight :=
  ((List.finRange 8).find? (columnFits a f j)).getD 0

private theorem cube_test : ∀ a : Index, cube a → ∀ f : Six → Six, Function.Injective f →
    (∀ i j, A a (f i) (f j)=A a i j) →
    Function.Injective (liftCol a f) ∧ (∀ i j, M a (f i) (liftCol a f j)=M a i j) ∧
      ∀ i j, B a (liftCol a f i) (liftCol a f j)=B a i j := by native_decide

theorem cube_extend (a : Index) (hc : cube a) (f : Equiv.Perm Six) (col : ∀ i j, A a (f i) (f j)=A a i j) :
    ∃ g : Equiv.Perm Eight, (∀ i j, M a (f i) (g j)=M a i j) ∧ ∀ i j, B a (g i) (g j)=B a i j := by
  obtain ⟨inj,rest⟩ := cube_test a hc f f.injective col
  exact ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp inj),rest⟩
end QGI.Coherent.SixEightCatalog
