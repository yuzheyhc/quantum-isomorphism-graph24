import DoubleEightBareClassify
import DoubleEightBareNormal
import DoubleEightInterfaceTransport

namespace QGI.DoubleEight.TwoColors

open ShoreCensus (V Coloring Homogeneous side PartitionIso)
open FixedInterface (named HasIntersectionNumbers)
open BareLaws (Bare ofColor)
open FiberRectangles (degree)

abbrev Raw := V ⊕ V → V ⊕ V → Nat
def cross (m : Raw) : Coloring := fun i j => m (.inl i) (.inr j)
def valency (m : Raw) (v : Nat) : Nat := degree (ofColor (cross m) v 0)

private theorem matrix_rows (B : Bare) : BareClassify.matrix (BareLex.rows B) = B := by
  funext i j
  fin_cases i <;> exact BareLex.mask_digit _ j

variable (m : Raw)
  (hl : Homogeneous (fun i j => m (.inl i) (.inl j)))
  (hr : Homogeneous (fun i j => m (.inr i) (.inr j)))
  (rectangle : ∀ i j x y, m i j = m x y → (side i, side j) = (side x, side y))
  (rev : ∀ i j x y, m i j = m x y → m j i = m y x) (products : HasIntersectionNumbers m)

include hl hr rectangle rev products

/-- Any individual cross color of row valency 2, 3 or 4 has one of the
specified bare anchor matrices after independent point relabelings.
The rest of the cross rectangle may have arbitrarily many colors. -/
theorem anchor_of_color (v : Nat)
    (hd : valency m v = 2 ∨ valency m v = 3 ∨ valency m v = 4) :
    ∃ a : Fin 13, a.val ∈ BareClassify.indices (valency m v) ∧ ∃ p q : Equiv.Perm V,
      ∀ i j, ofColor (cross m) v i j = BareClassify.anchor a (p i) (q j) := by
  let B := ofColor (cross m) v
  obtain ⟨r, s, row, col⟩ := (BareLaws.raw_necessary m hl hr rectangle rev products).1 v
  have balance := FiberRectangles.balance B row col
  have rd : ∀ i, degree (B i) = valency m v := fun i => (row i).trans (row 0).symm
  have cd : ∀ j, degree (BareLex.transpose B j) = valency m v := by
    intro j
    exact (col j).trans ((by omega : s = r).trans (row 0).symm)
  obtain ⟨p, q, enumerated⟩ := BareNormal.exists_enumerated B (valency m v) rd cd
  let e := Equiv.sumCongr p q
  let moved : Raw := fun i j => m (e i) (e j)
  have hs (x : V ⊕ V) : side (e x) = side x := by cases x <;> rfl
  have valid : BareLaws.Necessary (BareLex.move B p q) :=
    (BareLaws.raw_necessary moved (InterfaceTransport.move_homogeneous hl p)
      (InterfaceTransport.move_homogeneous hr q)
      (fun i j x y eq => by simpa only [hs] using rectangle (e i) (e j) (e x) (e y) eq)
      (fun i j x y => rev (e i) (e j) (e x) (e y))
      (InterfaceTransport.move_products products e)).2 v
  obtain ⟨a, ha, u, w, hu⟩ := BareClassify.classify hd enumerated (by rwa [matrix_rows])
  refine ⟨a, ha, p.symm.trans u, q.symm.trans w, fun i j => ?_⟩
  simpa only [matrix_rows, BareLex.move, Equiv.apply_symm_apply, Equiv.trans_apply] using
    hu (p.symm i) (q.symm j)

omit hl hr rectangle rev products in
private theorem pair_valency (a b : Nat) (hne : a ≠ b)
    (cover : ∀ i j, cross m i j = a ∨ cross m i j = b) :
    valency m a + valency m b = 8 := by
  have asSum (v : Nat) :
      valency m v = ∑ j : V, (if cross m 0 j = v then 1 else 0 : Nat) := by
    simp [valency, ofColor, degree]
  rw [asSum, asSum, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _j : V, (1 : Nat) := by
      apply Finset.sum_congr rfl
      intro j _
      rcases cover 0 j with h | h <;> simp [h, hne, Ne.symm hne]
    _ = 8 := by simp

private theorem two_color_layer (a b : Nat) (hne : a ≠ b)
    (cover : ∀ i j, cross m i j = a ∨ cross m i j = b)
    (hd : valency m a = 2 ∨ valency m a = 3 ∨ valency m a = 4) :
    ∃ k : Fin 88, InterfaceTransport.CrossIso (cross m) (named (Nonuniform.layer k).word) := by
  obtain ⟨s, _, p, q, cp⟩ := anchor_of_color m hl hr rectangle rev products a hd
  obtain ⟨k, u, w, mapped⟩ := BareClassify.anchor_layer s
  refine ⟨k, p.trans u, q.trans w, fun i j x y => ?_⟩
  have two : cross m i j = cross m x y ↔
      ofColor (cross m) a i j = ofColor (cross m) a x y := by
    rcases cover i j with h | h <;> rcases cover x y with h' | h' <;> simp [ofColor,h,h',hne,Ne.symm hne]
  exact two.trans (by rw [cp, cp]; exact mapped _ _ _ _)

/-- The full raw sixteen-point configuration is represented in the 636-row
catalogue whenever the cross rectangle has two named colors and neither is a
matching. The two lower bounds concern just row zero of the original matrix. -/
theorem every_raw_two_colors (a b : Nat) (hne : a ≠ b)
    (cover : ∀ i j, cross m i j = a ∨ cross m i j = b)
    (ha : 2 ≤ valency m a) (hb : 2 ≤ valency m b) :
    ∃ (t : Nat) (row : ShoreCheck.Word), Layers.matrices[t]? = some row ∧
      PartitionIso m (Placements.color row) := by
  have total := pair_valency m a b hne cover
  have hit : ∃ k : Fin 88, InterfaceTransport.CrossIso (cross m) (named (Nonuniform.layer k).word) := by
    by_cases small : valency m a ≤ 4
    · exact two_color_layer m hl hr rectangle rev products a b hne cover (by omega)
    · exact two_color_layer m hl hr rectangle rev products b a hne.symm
        (fun i j => (cover i j).symm) (by omega)
  obtain ⟨k, hk⟩ := hit
  exact InterfaceTransport.every_raw k m hk hl hr rectangle rev products

/-- The occupied entries of the named relation are the graph of a bijection
between the shores, expressed in the original point labels. -/
def IsMatching (v : Nat) : Prop :=
  ∃ e : Equiv.Perm V, ∀ i j, cross m i j = v ↔ e i = j

omit hl hr rectangle rev products in
/-- In any biregular palette, each used color of row-zero valency below two
is an actual point bijection, even with arbitrarily many other colors. -/
theorem matching_of_small_valency {c : Coloring} (regular : FiberRectangles.BiregularColors c)
    (v : Nat) (present : ∃ i j, c i j = v) (small : degree (ofColor c v 0) < 2) :
    ∃ e : Equiv.Perm V, ∀ i j, c i j = v ↔ e i = j := by
  let B := ofColor c v
  obtain ⟨r,s,rows,cols⟩ := regular v
  have balance := FiberRectangles.balance B rows cols
  obtain ⟨i,j,occupied⟩ := present
  have pos : 0 < degree (B i) := Finset.card_pos.mpr ⟨j, by simpa [B,ofColor] using occupied⟩
  change degree (B 0) < 2 at small
  have hi : degree (B i) = r := rows i
  have h₀ : degree (B 0) = r := rows 0
  have one : r = 1 := by omega
  have other : s = 1 := by omega
  choose f hf using fun x => Finset.card_eq_one.mp ((rows x).trans one)
  have spec (x y : V) : c x y = v ↔ f x = y := by
    have h := Finset.ext_iff.mp (hf x) y
    simpa [ofColor, eq_comm] using h
  have onto : Function.Surjective f := by
    intro y
    have hit : 0 < degree (fun x => B x y) := by rw [show degree (fun x => B x y) = s from cols y, other]; decide
    obtain ⟨x,hx⟩ := Finset.card_pos.mp hit
    exact ⟨x, (spec x y).mp (by simpa [B,ofColor] using hx)⟩
  exact ⟨Equiv.ofBijective f (Finite.surjective_iff_bijective.mp onto), spec⟩

private theorem matching_of_small (v : Nat) (present : ∃ i j, cross m i j = v)
    (small : valency m v < 2) : IsMatching m v :=
  matching_of_small_valency (BareLaws.raw_necessary m hl hr rectangle rev products).1 v present small

/-- Every genuine two-color cross rectangle either has an explicit matching
among its two colors or has a full point-isomorphic catalogue representative. -/
theorem matching_or_catalogue (a b : Nat) (hne : a ≠ b)
    (cover : ∀ i j, cross m i j = a ∨ cross m i j = b)
    (presentA : ∃ i j, cross m i j = a) (presentB : ∃ i j, cross m i j = b) :
    (IsMatching m a ∨ IsMatching m b) ∨
      ∃ (t : Nat) (row : ShoreCheck.Word), Layers.matrices[t]? = some row ∧
        PartitionIso m (Placements.color row) := by
  by_cases ha : 2 ≤ valency m a
  · by_cases hb : 2 ≤ valency m b
    · exact Or.inr (every_raw_two_colors m hl hr rectangle rev products a b hne cover ha hb)
    · exact Or.inl (Or.inr (matching_of_small m hl hr rectangle rev products b presentB (by omega)))
  · exact Or.inl (Or.inl (matching_of_small m hl hr rectangle rev products a presentA (by omega)))

end QGI.DoubleEight.TwoColors
