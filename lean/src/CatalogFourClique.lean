import CatalogRigidity

open scoped BigOperators

namespace QGI.CatalogRigidity
open ThetaBridge Intertwiner

/-- Count maps from the four labelled vertices of K₄. Each of its six edges
is tested when the later endpoint is chosen. -/
private def countK4 {n : Nat} (edge : Fin n → Fin n → Bool) : Nat :=
  ∑ i, ∑ j, if edge i j then
    ∑ k, if edge i k && edge j k then
      ∑ l, if edge i l && edge j l && edge k l then 1 else 0
    else 0
  else 0

/-- The number of graph homomorphisms K₄ → G. Vertices of G have no loops,
so a contributing assignment of the four labelled vertices is injective. -/
def orderedK4 {n : Nat} (G : Graph n) : Nat := countK4 G.edge

/-- The same six tests, run on the zero-one entries of a catalog matrix. -/
def fourCliqueNat {n : Nat} (a : NMat n) : Nat :=
  countK4 (fun i j => entry a i j == 1)

private theorem countK4_relabel {n : Nat} (edge : Fin n → Fin n → Bool)
    (e : Fin n ≃ Fin n) : countK4 (fun i j => edge (e i) (e j)) = countK4 edge := by
  unfold countK4
  apply Fintype.sum_equiv e
  intro i
  apply Fintype.sum_equiv e
  intro j
  by_cases hij : edge (e i) (e j) = true
  · simp only [hij, if_true]
    apply Fintype.sum_equiv e
    intro k
    by_cases hk : (edge (e i) (e k) && edge (e j) (e k)) = true
    · simp only [hk, if_true]
      apply Fintype.sum_equiv e
      intro l
      rfl
    · simp only [if_neg hk]
  · simp only [if_neg hij]

/-- The integral formula on any catalog labeling computes the graph count. -/
theorem fourCliqueNat_spec {n : Nat} {G : Graph n} {a : NMat n} {e : Fin n ≃ Fin n}
    (ha : Reads e a (adjacency G)) : fourCliqueNat a = orderedK4 G := by
  have edges : (fun i j => entry a i j == 1) = (fun i j => G.edge (e i) (e j)) := by
    funext i j
    have h := ha i j
    cases hij : G.edge (e i) (e j) with
    | false =>
      have h0 : (entry a i j : ℂ) = 0 := by simpa [adjacency, hij] using h
      have v : entry a i j = 0 := by exact_mod_cast h0
      simp [v]
    | true =>
      have h1 : (entry a i j : ℂ) = 1 := by simpa [adjacency, hij] using h
      have v : entry a i j = 1 := by exact_mod_cast h1
      simp [v]
  unfold fourCliqueNat orderedK4
  rw [edges]
  exact countK4_relabel G.edge e

end QGI.CatalogRigidity

namespace QGI.Literature

/-- Mančinska and Roberson, *Quantum isomorphism is equivalent to equality
of homomorphism counts from planar graphs*, Theorem 7.16 in arXiv:1910.06958.
Apply its forward direction for the commuting-operator model to K₄, which
has a planar drawing with one vertex inside a triangle. The four vertices of
the source are labelled in `orderedK4`. https://arxiv.org/abs/1910.06958 -/
axiom mancinska_roberson_K4 {n : Nat} {G H : Graph n} (q : QuantumIso G H) :
    CatalogRigidity.orderedK4 G = CatalogRigidity.orderedK4 H

end QGI.Literature

namespace QGI.CatalogRigidity
open ThetaBridge Intertwiner

theorem fourCliqueNat_sound {n : Nat} {G H : Graph n} {a b : NMat n}
    {e f : Fin n ≃ Fin n} (ha : Reads e a (adjacency G))
    (hb : Reads f b (adjacency H)) (q : QuantumIso G H) : fourCliqueNat a = fourCliqueNat b :=
  (fourCliqueNat_spec ha).trans ((Literature.mancinska_roberson_K4 q).trans
    (fourCliqueNat_spec hb).symm)

def key16 {n : Nat} (a : NMat n) := (key a, fourCliqueNat a)

theorem key16_sound {n : Nat} {G H : Graph n} {a b : NMat n}
    {e f : Fin n ≃ Fin n} (ha : Reads e a (adjacency G))
    (hb : Reads f b (adjacency H)) (q : QuantumIso G H) : key16 a = key16 b :=
  Prod.ext (key_sound ha hb q) (fourCliqueNat_sound ha hb q)

end QGI.CatalogRigidity
