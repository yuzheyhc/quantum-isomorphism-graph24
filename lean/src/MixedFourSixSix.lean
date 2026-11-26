import Lean

/- A local obstruction in the partition 4+6+6. Work over the naturals:
   the product word alone separates two entries of a single diagonal. -/
namespace QGI.MixedFourSixSix

inductive Fibre where
  | four | edges | halves

def size : Fibre → Nat
  | .four => 4
  | .edges => 6
  | .halves => 6

abbrev Rect (i j : Fibre) := Fin (size i) → Fin (size j) → Nat

def transpose {i j : Fibre} (a : Rect i j) : Rect j i := fun y x => a x y

def mul {i j k : Fibre} (a : Rect i j) (b : Rect j k) : Rect i k :=
  fun x z => ((List.finRange (size j)).map (fun y => a x y * b y z)).sum

/-- For each block of a coherent configuration, take the natural-valued
matrices constant on each basis relation. Transpose and ordinary matrix
product preserve membership. A single fibre has one diagonal colour. -/
structure ClosedBlocks where
  mem : (i j : Fibre) → Rect i j → Prop
  trans_mem : ∀ {i j} {a : Rect i j}, mem i j a → mem j i (transpose a)
  mul_mem : ∀ {i j k} {a : Rect i j} {b : Rect j k},
    mem i j a → mem j k b → mem i k (mul a b)
  diag_eq : ∀ {i} {a : Rect i i}, mem i i a →
    ∀ x y : Fin (size i), a x x = a y y

private def incidence (columns : List Nat) (x y : Nat) : Nat :=
  if (columns.getD y 0).testBit x then 1 else 0

/-- Columns 01, 02, 03, 12, 13, 23. Bit i records membership of point i. -/
def N : Rect .four .edges :=
  fun x y => incidence [3, 5, 9, 6, 10, 12] x.val y.val

/-- Columns 01, 01, 01, 23, 23, 23. -/
def B : Rect .four .halves :=
  fun x y => incidence [3, 3, 3, 12, 12, 12] x.val y.val

/-- W = (Bᵀ N)ᵀ (Bᵀ N), a word on the edge-labelled six-point fibre. -/
def W : Rect .edges .edges :=
  let t : Rect .halves .edges :=
    @mul .halves .four .edges (@transpose .four .halves B) N
  @mul .edges .halves .edges (@transpose .halves .edges t) t

private abbrev firstEdge : Fin (size .edges) := ⟨0, by decide⟩
private abbrev secondEdge : Fin (size .edges) := ⟨1, by decide⟩

theorem diagonal_values : W firstEdge firstEdge = 12 ∧ W secondEdge secondEdge = 6 := by decide

/-- After the common four-point side and the two six-point sides have been
labelled as above, the two proposed cross colours cannot coexist. -/
theorem mixed_types_impossible (c : ClosedBlocks)
    (hN : c.mem .four .edges N) (hB : c.mem .four .halves B) : False := by
  have ht := c.mul_mem (c.trans_mem hB) hN
  have hw : c.mem .edges .edges W := c.mul_mem (c.trans_mem ht) ht
  have h := c.diag_eq hw firstEdge secondEdge
  rw [diagonal_values.1, diagonal_values.2] at h
  exact (by decide : (12 : Nat) ≠ 6) h

/-- The three perfect matchings are indexed by the partner of point zero.
The two sides have complementary four-bit masks. -/
private def sideEntry (m : Fin 3) (side : Bool) (x : Fin 4) : Nat :=
  let mask := [3, 5, 9].getD m.val 0
  if (if side then mask else 15 - mask).testBit x.val then 1 else 0

/-- Each of the six columns independently chooses a side of the matching. -/
def matchingBlock (m : Fin 3) (side : Fin 6 → Bool) : Rect .four .halves :=
  fun x j => sideEntry m (side j) x

private def matchingEdge (m : Fin 3) : Fin 6 := ⟨m.val, by omega⟩

private def crossingEdge (m : Fin 3) : Fin 6 := if m.val = 0 then 1 else 0

private def overlap (m : Fin 3) (s : Bool) (e : Fin 6) : Nat :=
  ((List.finRange 4).map (fun x => sideEntry m s x * N x e)).sum

private theorem matching_overlap : ∀ (m : Fin 3) (s : Bool),
    overlap m s (matchingEdge m) * overlap m s (matchingEdge m) =
      4 * (if s then 1 else 0) := by decide

private theorem crossing_overlap : ∀ (m : Fin 3) (s : Bool),
    overlap m s (crossingEdge m) * overlap m s (crossingEdge m) = 1 := by decide

private theorem sum_four (js : List (Fin 6)) (f : Fin 6 → Nat) :
    (js.map (fun j => 4 * f j)).sum = 4 * (js.map f).sum := by
  induction js with
  | nil => rfl
  | cons i js ih => simp [ih, Nat.mul_add]

/-- The edge-incidence block and a matching block cannot coexist, for any
of the three matchings, any ordering of columns, and any side multiplicities. -/
theorem matching_types_impossible (c : ClosedBlocks) (m : Fin 3) (side : Fin 6 → Bool)
    (hN : c.mem .four .edges N) (hB : c.mem .four .halves (matchingBlock m side)) : False := by
  have ht := c.mul_mem (c.trans_mem hB) hN
  have hw := c.mul_mem (c.trans_mem ht) ht
  have h := c.diag_eq hw (matchingEdge m) (crossingEdge m)
  change ((List.finRange 6).map (fun j =>
    overlap m (side j) (matchingEdge m) * overlap m (side j) (matchingEdge m))).sum =
    ((List.finRange 6).map (fun j =>
    overlap m (side j) (crossingEdge m) * overlap m (side j) (crossingEdge m))).sum at h
  simp only [matching_overlap, crossing_overlap] at h
  rw [sum_four] at h
  change 4 * _ = 6 at h
  omega

end QGI.MixedFourSixSix
