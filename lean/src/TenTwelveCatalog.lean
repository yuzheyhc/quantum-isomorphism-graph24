import BinaryShoreLaws
import TenPointPetersen
import data.BinaryShoreMasks

namespace QGI.Coherent.TenTwelveCatalog
open BinaryShore
abbrev I := Fin 10
abbrev J := Fin 12
abbrev A := Fin 13
abbrev D := Fin 59
def left (a : A) : Table 10 := TenPointCross.cell a
def right (a : D) : Table 12 := EightTwelveCatalog.cell (EightTwelveCatalog.row 12 a.val)
def decode {n : Nat} (w : Nat) : Cell n := Finset.univ.filter fun i => w.testBit i.val=true
def pool {n : Nat} (data : Array (List Nat)) (key : Nat) : List (Cell n) := ((data[key]?).getD []).map decode
def bank {n : Nat} [NeZero n] (m : Table n) (candidates : List (Cell n)) (s : Cell n) :=
  candidates.filter fun t => profile m t=profile m s
def Simple {n : Nat} (l : List (Cell n)) (s : Cell n) := ∀ t∈l, t=s ∨ t=sᶜ
instance {n : Nat} (l : List (Cell n)) (s : Cell n) : Decidable (Simple l s) := by unfold Simple; infer_instance
def Odd (r s t : Cell 10) := ((r∩s).card+(r∩t).card+(s∩t).card)%2=1
instance (r s t : Cell 10) : Decidable (Odd r s t) := by unfold Odd; infer_instance
def predicted (m : Table 12) (s : Cell 12) (i j : J) := 5*count m s (first s) (m i j)/valency m (m i j)
def triangle (m : Table 12) (s : Cell 12) := ∃ i j k : J, (predicted m s i j+predicted m s i k+predicted m s j k)%2=0
def short (m : Table 12) (s : Cell 12) := ∀ i : J, (Finset.univ.filter fun j => predicted m s i j=5).card≤3
def leftBank (a : A) (s : Cell 10) := bank (left a) (pool BinaryShoreMasks.masks10x12 a.val) s
def rightBank (a : D) (s : Cell 12) := bank (right a) (pool BinaryShoreMasks.masks12x10 a.val) s

private def checkLeft (a : A) (s : Cell 10) := let b := leftBank a s
  decide (Simple b s ∨ a=2 ∨ ∀ x∈b, ∀ y∈b, ∀ z∈b, Odd x y z)
private def checkRight (a : D) (s : Cell 12) := let b := rightBank a s
  decide (Simple b s) || (decide (∃ i j k : J, (predicted (right a) s i j+predicted (right a) s i k+predicted (right a) s j k)%2=0) &&
    decide (∀ i : J, (Finset.univ.filter fun j => predicted (right a) s i j=5).card≤3))
attribute [local irreducible] TenPointCross.matrices EightTwelveCatalog.row EightTwelveCatalog.rows12
  BinaryShoreMasks.masks10x12 BinaryShoreMasks.masks12x10

set_option maxRecDepth 30000 in
private theorem left_complete : ∀ a : A, ((Finset.univ.powersetCard 5).filter fun s =>
    s∉pool BinaryShoreMasks.masks10x12 a.val ∧ Admits (left a) 6 s).card=0 := by native_decide
set_option maxRecDepth 30000 in
private theorem right_complete : ∀ a : D, ((Finset.univ.powersetCard 6).filter fun s =>
    s∉pool BinaryShoreMasks.masks12x10 a.val ∧ Admits (right a) 5 s).card=0 := by native_decide
set_option maxRecDepth 30000 in
private theorem ltested : ∀ a : A, (pool BinaryShoreMasks.masks10x12 a.val).all (checkLeft a)=true := by native_decide
set_option maxRecDepth 30000 in
private theorem rtested : ∀ a : D, (pool BinaryShoreMasks.masks12x10 a.val).all (checkRight a)=true := by native_decide
theorem positive : ∀ (a : D) (i j : J), 0<valency (right a) (right a i j) := by native_decide

private theorem listed {n : Nat} (l : List (Cell n)) {k} {p : Cell n → Prop} [DecidablePred p] {s : Cell n}
    (size : s.card=k) (adm : p s) (full : ((Finset.univ.powersetCard k).filter fun t => t∉l ∧ p t).card=0) : s∈l := by
  by_contra outside
  exact (Nat.ne_of_gt (Finset.card_pos.mpr ⟨s,Finset.mem_filter.mpr ⟨
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,size⟩,outside,adm⟩⟩)) full
theorem inLeft (a : A) {t s : Cell 10} (sz : t.card=5) (ht : Admits (left a) 6 t) (same : profile (left a) t=profile (left a) s) :
    t∈leftBank a s := List.mem_filter.mpr ⟨listed _ sz ht (left_complete a),decide_eq_true same⟩
theorem inRight (a : D) {t s : Cell 12} (sz : t.card=6) (ht : Admits (right a) 5 t) (same : profile (right a) t=profile (right a) s) :
    t∈rightBank a s := List.mem_filter.mpr ⟨listed _ sz ht (right_complete a),decide_eq_true same⟩
theorem left_cases (a : A) {s : Cell 10} (sz : s.card=5) (adm : Admits (left a) 6 s) :
    Simple (leftBank a s) s ∨ a=2 ∨ ∀ x∈leftBank a s, ∀ y∈leftBank a s, ∀ z∈leftBank a s, Odd x y z :=
  of_decide_eq_true (List.all_eq_true.mp (ltested a) _ (listed _ sz adm (left_complete a)))
theorem right_cases (a : D) {s : Cell 12} (sz : s.card=6) (adm : Admits (right a) 5 s) :
    Simple (rightBank a s) s ∨ triangle (right a) s ∧ short (right a) s := by
  have h := List.all_eq_true.mp (rtested a) _ (listed _ sz adm (right_complete a))
  simpa only [checkRight,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,triangle,short] using h

end QGI.Coherent.TenTwelveCatalog
