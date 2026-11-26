import TenTwelveCatalog
import ZivAvCoreQuantum
import data.EightFourteenFamilies

namespace QGI.Coherent.EightFourteenCatalog
open BinaryShore
open TenTwelveCatalog (bank pool Simple)
open private listed from TenTwelveCatalog
abbrev I := Fin 8
abbrev J := Fin 14
abbrev Axis := Fin 7
abbrev LK := Fin 21
abbrev RK := Fin 16
def left (a : LK) : Table 8 := EightTwelveCatalog.cell (EightTwelveCatalog.row 8 a.val)
def right (d : RK) : Table 14 := ZivAv.color ⟨d.val,by omega⟩
def point (j : Axis) (b : Bool) : J := ⟨2*j.val+b.toNat,by cases b <;> simp <;> omega⟩
def rankTwo (a : LK) := ∀ i j x y : I, left a i j=left a x y ↔ (i=j ↔ x=y)
def rowTest (a : LK) (s : Cell 8) := ∀ i j : I, i≠j →
    0<valency (left a) (left a i j) ∧ 7*count (left a) s (first s) (left a i j)=valency (left a) (left a i j)*3
def hard (a : RK) := a=1 ∨ a=4 ∨ a=7 ∨ a=13
def split (s : Cell 14) := ∀ j : Axis, point j false∈s ↔ point j true∉s
instance (a : LK) : Decidable (rankTwo a) := by unfold rankTwo; infer_instance
instance (a : LK) (s : Cell 8) : Decidable (rowTest a s) := by unfold rowTest; infer_instance
instance (a : RK) : Decidable (hard a) := by unfold hard; infer_instance
instance (s : Cell 14) : Decidable (split s) := by unfold split; infer_instance
def lb (a : LK) (s : Cell 8) := bank (left a) (pool EightFourteenInput.masks8 a.val) s
def rb (a : RK) (s : Cell 14) := bank (right a) (pool EightFourteenInput.masks14 a.val) s
private def checkL (a : LK) (s : Cell 8) := decide (Simple (lb a s) s ∨ rankTwo a ∧ rowTest a s)
private def checkR (a : RK) (s : Cell 14) := decide (Simple (rb a s) s ∨ hard a ∧ ∀ t∈rb a s, split t)
attribute [local irreducible] EightTwelveCatalog.row EightTwelveCatalog.rows8 ZivAv.cores14
  EightFourteenInput.masks8 EightFourteenInput.masks14
set_option maxRecDepth 30000 in
private theorem lc : ∀ a : LK, ((Finset.univ.powersetCard 4).filter fun s =>
    s∉pool EightFourteenInput.masks8 a.val ∧ Admits (left a) 7 s).card=0 := by native_decide
set_option maxRecDepth 30000 in
private theorem rc : ∀ a : RK, ((Finset.univ.powersetCard 7).filter fun s =>
    s∉pool EightFourteenInput.masks14 a.val ∧ Admits (right a) 4 s).card=0 := by native_decide
set_option maxRecDepth 30000 in
private theorem lt : ∀ a : LK, (pool EightFourteenInput.masks8 a.val).all (checkL a)=true := by native_decide
set_option maxRecDepth 30000 in
private theorem rt : ∀ a : RK, (pool EightFourteenInput.masks14 a.val).all (checkR a)=true := by native_decide
theorem lmem (a : LK) {s t : Cell 8} (size : t.card=4) (ok : Admits (left a) 7 t) (eq : profile (left a) t=profile (left a) s) : t∈lb a s :=
  List.mem_filter.mpr ⟨listed _ size ok (lc a),decide_eq_true eq⟩
theorem rmem (a : RK) {s t : Cell 14} (size : t.card=7) (ok : Admits (right a) 4 t) (eq : profile (right a) t=profile (right a) s) : t∈rb a s :=
  List.mem_filter.mpr ⟨listed _ size ok (rc a),decide_eq_true eq⟩
theorem left_cases (a : LK) {s : Cell 8} (size : s.card=4) (ok : Admits (left a) 7 s) :
    Simple (lb a s) s ∨ rankTwo a ∧ rowTest a s :=
  of_decide_eq_true (List.all_eq_true.mp (lt a) _ (listed _ size ok (lc a)))
theorem right_cases (a : RK) {s : Cell 14} (size : s.card=7) (ok : Admits (right a) 4 s) :
    Simple (rb a s) s ∨ hard a ∧ ∀ t∈rb a s, split t :=
  of_decide_eq_true (List.all_eq_true.mp (rt a) _ (listed _ size ok (rc a)))
theorem first_sixteen : ∀ a : ZivAv.Index, (∀ i : J, ZivAv.color a i i=ZivAv.color a 0 0) → a.val<16 := by native_decide
end QGI.Coherent.EightFourteenCatalog
