import Mathlib.Data.Fintype.Basic
import data.DoubleEightCatalog
import data.DoubleEightUniformInput

namespace QGI.DoubleEight.Uniform

open UniformInput

/-- Colors of the uniform interface are 0 and 1, one for each direction.
The two shores use disjoint colors, including their own diagonals. -/
def model (a b : Fin 21) (i j : Fin 16) : Nat :=
  if i.val < 8 then
    if j.val < 8 then 2 + 2 * (shores[a.val]!.getD (8 * i.val + j.val) 0) else 0
  else if j.val < 8 then 1
  else 3 + 2 * (shores[b.val]!.getD (8 * (i.val - 8) + (j.val - 8)) 0)

def color (m : Array Nat) (i j : Fin 16) : Nat := m.getD (16 * i.val + j.val) 0

def rows : Array (Array Nat) := Input.matrices.toArray

def isUniform (m : Array Nat) : Bool :=
  decide (∀ i j : Fin 8,
    m.getD (16 * i.val + 8 + j.val) 0 = m.getD 8 0 ∧
    m.getD (16 * (8 + i.val) + j.val) 0 = m.getD 128 0)

def uniformRows : List Nat :=
  (List.range rows.size).filter fun k => isUniform (rows.getD k #[])

/-- Triangular row-major index for the sorted shore pair. -/
def witness (a b : Fin 21) : Witness :=
  witnesses.getD (a.val * (43 - a.val) / 2 + (b.val - a.val)) default

private def point (p : Array Nat) (i : Fin 16) : Fin 16 :=
  ⟨p.getD i.val 0 % 16, Nat.mod_lt _ (by decide)⟩

private def Valid (a b : Fin 21) (w : Witness) (m : Array Nat) : Prop :=
  w.left = a.val ∧ w.right = b.val ∧ w.row < rows.size ∧ m.size = 256 ∧
  (∀ i : Fin 16, point w.inverse (point w.points i) = i) ∧
  (∀ i : Fin 16, point w.points (point w.inverse i) = i) ∧
  (∀ i j : Fin 16, w.colors[model a b i j]? =
    some (color m (point w.points i) (point w.points j))) ∧
  (∀ i j : Fin 16, w.inverseColors[color m (point w.points i) (point w.points j)]? =
    some (model a b i j))

private instance (a b : Fin 21) (w : Witness) (m : Array Nat) :
    Decidable (Valid a b w m) := by unfold Valid; infer_instance

private theorem all_valid (a b : Fin 21) (h : a ≤ b) :
    Valid a b (witness a b) (rows.getD (witness a b).row #[]) := by
  revert h b a
  native_decide

/-- A permutation of the sixteen points identifies both complete partitions
of the ordered pairs. This permits arbitrary bijective renaming of colors. -/
def Realized (a b : Fin 21) (m : Array Nat) : Prop :=
  ∃ f : Fin 16 ≃ Fin 16, ∀ i j k l : Fin 16,
    model a b i j = model a b k l ↔ color m (f i) (f j) = color m (f k) (f l)

/-- Each sorted pair of the supplied shore matrices is realized on its
specific catalogue row. Both directions of color preservation are certified. -/
theorem realizes_pair (a b : Fin 21) (hab : a ≤ b) :
    (witness a b).row < rows.size ∧
    Realized a b (rows.getD (witness a b).row #[]) := by
  let w := witness a b
  let m := rows.getD w.row #[]
  obtain ⟨_, _, hrow, _, hl, hr, hc, hd⟩ := all_valid a b hab
  let f : Fin 16 ≃ Fin 16 :=
    ⟨point w.points, point w.inverse, hl, hr⟩
  refine ⟨hrow, f, ?_⟩
  intro i j k l
  constructor
  · intro h
    apply Option.some.inj
    exact (hc i j).symm.trans ((congrArg (fun x : Nat => w.colors[x]?) h).trans (hc k l))
  · intro h
    apply Option.some.inj
    exact (hd i j).symm.trans ((congrArg (fun x : Nat => w.inverseColors[x]?) h).trans (hd k l))

/-- Direct scan of the input dimensions and the two 8 by 8 interface blocks. -/
theorem catalogue_counts :
    shores.size = 21 ∧ (shores.all (fun s => s.size == 64)) = true ∧
    rows.size = 636 ∧ (rows.all (fun m => m.size == 256)) = true ∧
    witnesses.size = 231 ∧ uniformRows.length = 231 ∧
    (witnesses.toList.map Witness.row).Nodup := by native_decide

/-- A row has a uniform interface in both directions exactly when it is the
assigned row of a sorted pair. The bound uses the observed catalogue length. -/
theorem uniform_iff_pair (r : Fin 636) :
    isUniform (rows.getD r.val #[]) = true ↔
      ∃ a b : Fin 21, a ≤ b ∧ (witness a b).row = r.val := by
  revert r
  native_decide

theorem uniform_row_realized (r : Fin 636) (h : isUniform (rows.getD r.val #[]) = true) :
    ∃ a b : Fin 21, a ≤ b ∧ Realized a b (rows.getD r.val #[]) := by
  obtain ⟨a, b, hab, hr⟩ := (uniform_iff_pair r).mp h
  exact ⟨a, b, hab, hr ▸ (realizes_pair a b hab).2⟩

end QGI.DoubleEight.Uniform
