import SixTenCrossEnum
import data.SixTenCross
import Mathlib.Data.Fintype.EquivFin

namespace QGI.SixTen.Cross

def splitModel : Matrix := fun i j => decide ((i.val < 3) ↔ (j.val < 5))
def designCodes : Array Nat := #[7,11,21,26,28,38,41,44,49,50]
def design : Matrix := fun i j => bit (designCodes.getD j.val 0) i

private def lhs (r : Row) (x : L) : L := ⟨(r.left.getD x.val 6) % 6, Nat.mod_lt _ (by decide)⟩
private def rhs (r : Row) (x : R) : R := ⟨(r.right.getD x.val 10) % 10, Nat.mod_lt _ (by decide)⟩

private def mapsOK (r : Row) : Bool :=
  decide ((∀ i j, lhs r i = lhs r j → i = j) ∧
          (∀ i j, rhs r i = rhs r j → i = j) ∧
          ∀ i j, asMatrix r.cols i j = (if r.split then splitModel else design) (lhs r i) (rhs r j))

private theorem goodMaps : records.all mapsOK = true := by native_decide

private def keys := records.map Row.cols

private def audit : Bool :=
  let raw := regularMatrices
  let accepted := raw.filter uniformHist
  raw.length == 12904 && accepted.length == 22 && accepted.all (fun cs => decide (cs ∈ keys))

private theorem checked : audit = true := by native_decide

theorem counts : regularMatrices.length = 12904 ∧ (regularMatrices.filter uniformHist).length = 22 := by
  have h := checked
  simp only [audit,Bool.and_eq_true,beq_iff_eq] at h
  exact h.1

/-- The table has no completeness hypothesis. Both maps permute actual points;
all allowed masks enter the same finite row/column Gram test. -/
theorem classify {cols : List Nat} (mem : cols ∈ regularMatrices) (hist : uniformHist cols = true) :
    ∃ (p : Equiv.Perm L) (q : Equiv.Perm R),
      (∀ i j, asMatrix cols i j = splitModel (p i) (q j)) ∨
      (∀ i j, asMatrix cols i j = design (p i) (q j)) := by
  have h := checked
  simp only [audit,Bool.and_eq_true] at h
  have key := of_decide_eq_true (List.all_eq_true.mp h.2 cols (List.mem_filter.mpr ⟨mem,hist⟩))
  obtain ⟨r,inside,rfl⟩ := List.mem_map.mp key
  obtain ⟨lp,rp,eq⟩ := of_decide_eq_true (List.all_eq_true.mp goodMaps r inside)
  let p := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp lp)
  let q := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp rp)
  refine ⟨p,q,?_⟩
  cases b : r.split with
  | true => left; simpa only [b,if_true] using eq
  | false => right; simpa only [b,Bool.false_eq_true,if_false] using eq

end QGI.SixTen.Cross