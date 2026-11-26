import data.DoubleEightCatalog
import Mathlib.Data.Fintype.EquivFin

namespace QGI.DoubleEight.Layers

structure Layer where
  word : Array Nat
  inputs : Nat
  groupOrder : Nat
  left : Nat
  right : Nat
  product : Nat
  representedMass : Nat
  orbits : Nat
  deriving Inhabited

structure MapRow where
  layer : Nat
  stabilizer : Nat
  points : Array Nat
  deriving Inhabited

private def lines (s : String) : List String :=
  (s.splitOn "\n").map String.trim |>.filter (· != "")

private def readLayer (s : String) : Option Layer := do
  let [word,i,g,l,r,p,m,o] := s.splitOn "\t" | none
  let cells ← word.toList.mapM fun c => if '0' ≤ c && c ≤ '3' then some (c.toNat - 48) else none
  return ⟨cells.toArray, ← i.toNat?, ← g.toNat?, ← l.toNat?, ← r.toNat?, ← p.toNat?,
    ← m.toNat?, ← o.toNat?⟩

def layers : Array Layer :=
  (((lines (include_str "data/double-eight-layers.tsv")).drop 1).mapM readLayer).getD [] |>.toArray

private def readMap (s : String) : Option MapRow := do
  let i :: h :: p ← (s.splitOn " ").mapM String.toNat? | none
  return ⟨i, h, p.toArray⟩

def maps : Array MapRow :=
  ((lines (include_str "data/double-eight-layer-map.txt")).mapM readMap).getD [] |>.toArray

def matrices : Array (Array Nat) := Input.matrices.toArray

private def atCell (a : Array Nat) (k : Nat) : Nat := a[k]?.getD 256

def crossColor (l : Layer) (x : Fin 64) : Nat := atCell l.word x.val

def entry (m : Array Nat) (i j : Fin 16) : Nat := atCell m (16 * i.val + j.val)

def lhs (x : Fin 64) : Fin 16 := ⟨x.val / 8, by omega⟩
def rhs (x : Fin 64) : Fin 16 := ⟨8 + x.val % 8, by omega⟩

private def vertex (w : MapRow) (i : Fin 16) : Fin 16 :=
  ⟨atCell w.points i.val % 16, Nat.mod_lt _ (by decide)⟩

/-- The actual relabeling can exchange the two shores. It preserves and
reflects equality of all named cross-color cells, including after an exchange. -/
def Aligns (l : Layer) (m : Array Nat) (f : Fin 16 → Fin 16) : Prop :=
  (∀ i j : Fin 16, i.val / 8 = j.val / 8 ↔ (f i).val / 8 = (f j).val / 8) ∧
  ∀ x y : Fin 64, crossColor l x = crossColor l y ↔
    entry m (f (lhs x)) (f (rhs x)) = entry m (f (lhs y)) (f (rhs y))

private instance (l : Layer) (m : Array Nat) (f : Fin 16 → Fin 16) : Decidable (Aligns l m f) := by
  unfold Aligns
  infer_instance

private def checkedMap (i : Nat) : Bool := Id.run do
  let some w := maps[i]? | return false
  let some l := layers[w.layer]? | return false
  let some m := matrices[i]? | return false
  return w.points.size == 16 && w.points.all (· < 16) && m.size == 256 &&
    decide (∀ a b : Fin 16, vertex w a = vertex w b → a = b) &&
    decide (Aligns l m (vertex w))

set_option maxRecDepth 100000 in
private theorem checkedMaps : (List.range 636).all checkedMap = true := by native_decide

/-- Every catalog row carries an actual point permutation into its assigned
interface stratum. The target is one of the original 89 interface words. -/
theorem catalog_row_alignment (i : Fin 636) :
    ∃ w l m, maps[i.val]? = some w ∧ layers[w.layer]? = some l ∧ matrices[i.val]? = some m ∧
      ∃ f : Fin 16 ≃ Fin 16, Aligns l m f := by
  have h := List.all_eq_true.mp checkedMaps i.val (List.mem_range.mpr i.isLt)
  cases hw : maps[i.val]? with
  | none => simp [checkedMap, hw, Id.run] at h
  | some w =>
    cases hl : layers[w.layer]? with
    | none => simp [checkedMap, hw, hl, Id.run] at h
    | some l =>
      cases hm : matrices[i.val]? with
      | none => simp [checkedMap, hw, hl, hm, Id.run] at h
      | some m =>
        simp [checkedMap, hw, hl, hm, Id.run] at h
        exact ⟨w, l, m, rfl, hl, rfl, Equiv.ofBijective (vertex w)
          (Finite.injective_iff_bijective.mp h.1.2), h.2⟩

def assigned (i : Nat) : List MapRow := maps.toList.filter (fun w => w.layer == i)

def Layer.MassMatches (l : Layer) (rows : List MapRow) : Prop :=
  l.word.size = 64 ∧ 0 < l.groupOrder ∧ rows.length = l.orbits ∧
  (∀ w ∈ rows, 0 < w.stabilizer ∧ l.groupOrder % w.stabilizer = 0) ∧
  (rows.map (fun w => l.groupOrder / w.stabilizer)).sum = l.representedMass ∧
  l.representedMass = l.product ∧ l.product = l.left * l.right

private instance (l : Layer) (rows : List MapRow) : Decidable (l.MassMatches rows) := by
  unfold Layer.MassMatches
  infer_instance

/-- Quotients use the stabilizer orders in the replayed data. Their
interpretation as orders of the actual automorphism groups is independently
checked by the graph isomorphism computations. -/
theorem layer_masses : ∀ i : Fin 89, (layers[i.val]!).MassMatches (assigned i.val) := by
  native_decide

theorem totals :
    layers.size = 89 ∧ maps.size = 636 ∧ matrices.size = 636 ∧
    (layers.toList.map Layer.inputs).sum = 254 ∧
    (layers.toList.filter (fun l => 0 < l.product)).length = 16 ∧
    (layers.toList.map Layer.product).sum = 125564305 ∧
    (layers.toList.map Layer.orbits).sum = 636 := by native_decide

end QGI.DoubleEight.Layers
