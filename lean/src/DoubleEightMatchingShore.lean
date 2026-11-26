import DoubleEightMatchingExtension
import SmallConfigurationInput
import Batteries.Tactic.OpenPrivate

namespace QGI.Literature
open DoubleEight.ShoreCensus

/-- Matan Ziv-Av, *Enumeration of coherent configurations of order at most
15* (2018), §2.2 pp. 67–68, Tables 2–3. Among association schemes up to
30 points the complete tables of nonisomorphic algebraically isomorphic
pairs and proper algebraic automorphisms have no entry of order eight.
Hence every prescribed algebraic isomorphism at order eight is induced
by a vertex bijection: choose any point isomorphism and correct its
action on the colors by a point-induced algebraic automorphism.
The hypothesis here names the used basic relations on both shores with
the same integers. The specified algebraic isomorphism is their identity.
The author's computational verification is discussed in §2.3.
https://actamath.savbb.sk/pdf/aumb2605.pdf -/
theorem zivAv_named_eight (m n : Coloring) (hm : Homogeneous m) (hn : Homogeneous n)
    (used : ∀ a, (∃ i j, m i j = a) ↔ ∃ u v, n u v = a)
    (products : ∀ a b i j u v, m i j = n u v → intersection m a b i j = intersection n a b u v) :
    ∃ e : Equiv.Perm V, ∀ i j, m i j = n (e i) (e j) := by
  have cfg (c : Coloring) (h : Homogeneous c) : Coherent.SmallUnion.Configuration c :=
    ⟨fun i j x eq => (h.diagonal i j).mp (eq.trans ((h.diagonal x x).mpr rfl)),
     h.transpose, fun a b i j x y eq => h.products i j x y eq a b⟩
  exact zivAv_named_small_configuration (by decide) (by decide) (cfg m hm) (cfg n hn) used products

end QGI.Literature

namespace QGI.DoubleEight.MatchingExtension
open ShoreCensus (V side Homogeneous intersection)
open scoped BigOperators
open private middle from DoubleEightMatchingExtension

def leftTable (m : Coloring) : ShoreCensus.Coloring := fun i j => m (.inl i) (.inl j)

def LeftDiagonal (m : Coloring) (a : Nat) : Prop :=
  ∀ x y, m x y = a ↔ ∃ i : V, x = .inl i ∧ y = .inl i

def Rectangle (m : Coloring) : Prop :=
  ∀ i j k l, m i j = m k l → (side i,side j) = (side k,side l)

private theorem same_left {m n : Coloring} {d : Nat} (hm : LeftDiagonal m d)
    (hn : LeftDiagonal n d) (common : CommonProducts m n) (i j : V) (x y : X)
    (eq : leftTable m i j = n x y) : ∃ u v : V, x = .inl u ∧ y = .inl v := by
  obtain ⟨w,hw,_⟩ := middle common eq (.inl i)
  obtain ⟨z,_,hz⟩ := middle common eq (.inl j)
  obtain ⟨u,hu,_⟩ := (hn x w).mp (hw.trans ((hm _ _).mpr ⟨i,rfl,rfl⟩))
  obtain ⟨v,_,hv⟩ := (hn z y).mp (hz.trans ((hm _ _).mpr ⟨j,rfl,rfl⟩))
  exact ⟨u,v,hu,hv⟩

private theorem left_occurs {m n : Coloring} {d : Nat} (hm : LeftDiagonal m d)
    (hn : LeftDiagonal n d) (common : CommonProducts m n)
    (hit : ∀ i j, ∃ x y, m i j = n x y) {a : Nat}
    (used : ∃ i j, leftTable m i j = a) : ∃ x y, leftTable n x y = a := by
  obtain ⟨i,j,rfl⟩ := used
  obtain ⟨x,y,eq⟩ := hit (.inl i) (.inl j)
  obtain ⟨u,v,rfl,rfl⟩ := same_left hm hn common i j x y eq
  exact ⟨u,v,eq.symm⟩

private theorem reduce_count {m : Coloring} (rect : Rectangle m) {a : Nat}
    (used : ∃ i j, leftTable m i j = a) (b : Nat) (x y : V) :
    (∑ w : X, if m (.inl x) w = a ∧ m w (.inl y) = b then 1 else 0 : Nat) =
    intersection (leftTable m) a b x y := by
  obtain ⟨i,j,rfl⟩ := used
  have forbid (z : V) : m (.inl x) (.inr z) ≠ leftTable m i j := by
    intro h
    have f := rect _ _ _ _ h
    simp [side] at f
  simp only [Fintype.sum_sum_type,forbid,false_and,if_false,Finset.sum_const_zero,add_zero]
  rfl

/-- Equal full intersection data restrict to the prescribed association
of the two left shores, including the exact names of all used relations. -/
theorem left_realized {m n : Coloring} {d : Nat} (diagM : LeftDiagonal m d) (diagN : LeftDiagonal n d)
    (rectM : Rectangle m) (rectN : Rectangle n) (hm : Homogeneous (leftTable m))
    (hn : Homogeneous (leftTable n)) (common : CommonProducts m n)
    (forth : ∀ i j, ∃ x y, m i j = n x y) (back : ∀ x y, ∃ i j, n x y = m i j) :
    ∃ e : Equiv.Perm V, ∀ i j, m (.inl i) (.inl j) = n (.inl (e i)) (.inl (e j)) := by
  have swapped : CommonProducts n m := fun a b _ _ _ _ eq => (common a b _ _ _ _ eq.symm).symm
  have used (a : Nat) : (∃ i j, leftTable m i j = a) ↔ ∃ x y, leftTable n x y = a :=
    ⟨left_occurs diagM diagN common forth, left_occurs diagN diagM swapped back⟩
  apply Literature.zivAv_named_eight (leftTable m) (leftTable n) hm hn used
  intro a b i j u v eq
  by_cases present : ∃ i j, leftTable m i j = a
  · rw [← reduce_count rectM present, ← reduce_count rectN ((used _).mp present)]
    exact common a b _ _ _ _ eq
  · have absent := mt (used a).mpr present
    push_neg at absent present
    simp [intersection,absent,present]

theorem homogeneous_rename {m n : ShoreCensus.Coloring}
    (same : ∀ i j x y, m i j = m x y ↔ n i j = n x y) (h : Homogeneous m) : Homogeneous n := by
  refine ⟨fun i j => (same i j 0 0).symm.trans (h.diagonal i j),
    fun i j x y eq => (same _ _ _ _).mp (h.transpose _ _ _ _ ((same _ _ _ _).mpr eq)),?_⟩
  have prods : FixedInterface.HasIntersectionNumbers m :=
    fun a b i j x y eq => h.products i j x y eq a b
  exact fun i j x y eq a b => FixedInterface.rename_products same prods a b i j x y eq

end QGI.DoubleEight.MatchingExtension