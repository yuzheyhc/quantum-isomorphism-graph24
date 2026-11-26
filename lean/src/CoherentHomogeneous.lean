import Intertwiner

noncomputable section

namespace QGI
namespace Coherent

abbrev Mat (n : Nat) := Intertwiner.Mat n

def ones (n : Nat) : Mat n := fun _ _ => 1

def schur {n : Nat} (M N : Mat n) : Mat n := fun i j => M i j * N i j

/-- A complex coherent algebra on the labelled vertices, in the sense of
Lupini–Mančinska–Roberson §2.3. Its basis relations may be directed. -/
structure CoherentAlgebra (n : Nat) where
  space : Submodule ℂ (Mat n)
  one_mem : (1 : Mat n) ∈ space
  ones_mem : ones n ∈ space
  mul_mem : ∀ {M N}, M ∈ space → N ∈ space → M * N ∈ space
  schur_mem : ∀ {M N}, M ∈ space → N ∈ space → schur M N ∈ space
  adjoint_mem : ∀ {M}, M ∈ space → Matrix.conjTranspose M ∈ space

/-- The intersection of all coherent algebras containing the adjacency matrix. -/
def closure {n : Nat} (G : Graph n) : CoherentAlgebra n where
  space := {
    carrier := {M | ∀ C : CoherentAlgebra n, Intertwiner.adjacency G ∈ C.space → M ∈ C.space}
    zero_mem' := fun C _ => C.space.zero_mem
    add_mem' := fun hM hN C hG => C.space.add_mem (hM C hG) (hN C hG)
    smul_mem' := fun c _ hM C hG => C.space.smul_mem c (hM C hG) }
  one_mem := fun C _ => C.one_mem
  ones_mem := fun C _ => C.ones_mem
  mul_mem := fun hM hN C hG => C.mul_mem (hM C hG) (hN C hG)
  schur_mem := fun hM hN C hG => C.schur_mem (hM C hG) (hN C hG)
  adjoint_mem := fun hM C hG => C.adjoint_mem (hM C hG)

theorem adjacency_mem {n : Nat} (G : Graph n) :
    Intertwiner.adjacency G ∈ (closure G).space := fun _ hG => hG

/-- A single diagonal relation: the diagonal part of each algebra element is scalar. -/
def CoherentAlgebra.Homogeneous {n : Nat} (C : CoherentAlgebra n) : Prop :=
  ∀ M ∈ C.space, ∃ c : ℂ, schur M 1 = c • (1 : Mat n)

def IsHomogeneous {n : Nat} (G : Graph n) : Prop := (closure G).Homogeneous

/-- A bijection of the two matrix spaces preserving their coherent-algebra operations.
The ambient function has no specified values outside the source space. -/
structure AlgebraIso {n : Nat} (C D : CoherentAlgebra n) where
  map : Mat n → Mat n
  mapsTo : ∀ M ∈ C.space, map M ∈ D.space
  injectiveOn : ∀ M ∈ C.space, ∀ N ∈ C.space, map M = map N → M = N
  surjectiveOn : ∀ N ∈ D.space, ∃ M ∈ C.space, map M = N
  map_one : map 1 = 1
  map_ones : map (ones n) = ones n
  map_add : ∀ M ∈ C.space, ∀ N ∈ C.space, map (M + N) = map M + map N
  map_smul : ∀ c : ℂ, ∀ M ∈ C.space, map (c • M) = c • map M
  map_mul : ∀ M ∈ C.space, ∀ N ∈ C.space, map (M * N) = map M * map N
  map_schur : ∀ M ∈ C.space, ∀ N ∈ C.space, map (schur M N) = schur (map M) (map N)
  map_adjoint : ∀ M ∈ C.space, map (Matrix.conjTranspose M) = Matrix.conjTranspose (map M)

def AlgebraIso.Realized {n : Nat} {C D : CoherentAlgebra n} (e : AlgebraIso C D) : Prop :=
  ∃ f : Fin n ≃ Fin n, ∀ M ∈ C.space, ∀ x y, M x y = e.map M (f x) (f y)

/-- The three basis relations of an oriented rank-three scheme are the diagonal,
the arcs of the tournament and the reverse arcs. Only this implication of the
classification of the exceptional schemes is needed. -/
def CoherentAlgebra.HasTournamentBasis {n : Nat} (C : CoherentAlgebra n) : Prop :=
  ∃ arc : Fin n → Fin n → Bool,
    (∀ i j, i ≠ j → arc i j = !(arc j i)) ∧
    ∀ M ∈ C.space, ∃ a b c : ℂ, ∀ i j,
      M i j = if i = j then a else if arc i j then b else c

/-- A symmetric matrix cannot distinguish the two orientations of an arc.
Consequently a coherent-algebra isomorphism fixes every such matrix, even
when the isomorphism does not arise from a point permutation. -/
theorem AlgebraIso.fixes_tournament_symmetric {n : Nat} {C D : CoherentAlgebra n}
    (e : AlgebraIso C D) (ht : C.HasTournamentBasis) {M : Mat n} (hM : M ∈ C.space)
    (hs : ∀ i j, M i j = M j i) : e.map M = M := by
  obtain ⟨arc, flip, const⟩ := ht
  obtain ⟨a, b, c, h⟩ := const M hM
  have hexpr : M = (a - b) • (1 : Mat n) + b • ones n := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [h, ones, Matrix.one_apply]
    · have off : M i j = b := by
        cases he : arc i j with
        | true => simp [h, hij, he]
        | false =>
          have hrev : arc j i = true := by
            have hf := flip i j hij
            cases hr : arc j i <;> simp_all
          rw [hs i j, h j i]
          simp [Ne.symm hij, hrev]
      simp [off, hij, ones, Matrix.one_apply]
  calc
    e.map M = e.map ((a - b) • (1 : Mat n) + b • ones n) := congrArg e.map hexpr
    _ = (a - b) • (1 : Mat n) + b • ones n := by
      rw [e.map_add _ (C.space.smul_mem _ C.one_mem) _ (C.space.smul_mem _ C.ones_mem),
        e.map_smul _ _ C.one_mem, e.map_smul _ _ C.ones_mem, e.map_one, e.map_ones]
    _ = M := hexpr.symm

theorem AlgebraIso.homogeneous_target {n : Nat} {C D : CoherentAlgebra n}
    (e : AlgebraIso C D) (hC : C.Homogeneous) : D.Homogeneous := by
  intro N hN
  obtain ⟨M, hM, rfl⟩ := e.surjectiveOn N hN
  obtain ⟨c, hc⟩ := hC M hM
  refine ⟨c, ?_⟩
  calc
    schur (e.map M) 1 = schur (e.map M) (e.map 1) := by rw [e.map_one]
    _ = e.map (schur M 1) := (e.map_schur M hM 1 C.one_mem).symm
    _ = e.map (c • (1 : Mat n)) := congrArg e.map hc
    _ = c • (1 : Mat n) := by rw [e.map_smul c 1 C.one_mem, e.map_one]

end Coherent

namespace Literature
open Coherent

/-- Lupini, Mančinska and Roberson, *Nonlocal Games and Quantum Permutation
Groups*, Theorem 4.4 and Corollary 4.7. The coherent-algebra isomorphism
carries the adjacency of the first graph to that of the second.
https://arxiv.org/pdf/1712.01820 -/
axiom lmr_coherentIso_of_qc {n : Nat} {G H : Graph n} (q : QuantumIso G H) :
    ∃ e : AlgebraIso (closure G) (closure H),
      e.map (Intertwiner.adjacency G) = Intertwiner.adjacency H

/-- Ziv-Av, *Enumeration of coherent configurations of order at most 15*
(2018), §2.2, Tables 2 and 3, pp. 67–68. Both tables concern association
schemes through order 30. At these four orders Table 2 has no pair of distinct
isomorphism classes with the same intersection numbers, and Table 3 has no
proper algebraic automorphism. Given an algebraic isomorphism, take a point
isomorphism by Table 2. Their difference is an algebraic automorphism, hence
also induced by a point permutation by Table 3. This is that classification
consequence in the matrix presentation of association schemes (LMR §2.3, §4.3).
Ziv-Av §2.3 discusses the computational provenance of the classification.
https://actamath.savbb.sk/pdf/aumb2605.pdf -/
axiom zivAv_schemeIso_realized {n : Nat} (hn : n = 17 ∨ n = 20 ∨ n = 21 ∨ n = 22)
    {C D : CoherentAlgebra n} (hC : C.Homogeneous) (hD : D.Homogeneous) (e : AlgebraIso C D) :
    e.Realized

/-- Ziv-Av, Tables 2, 3 and §4.2, pp. 67–68, 71. At order 19 the unique
exceptional algebraic isomorphism class consists of schemes 2,3. At 23 the
exceptional class is 2 through 20. Table 3 has no proper automorphism at 19;
at 23 its entries are 2 through 19, all in the same class. Section 4.2
identifies both exceptional classes as the schemes of doubly regular tournaments.
https://actamath.savbb.sk/pdf/aumb2605.pdf -/
axiom zivAv_tournament_exceptions {n : Nat} (hn : n = 19 ∨ n = 23)
    {C D : CoherentAlgebra n} (hC : C.Homogeneous) (hD : D.Homogeneous) (e : AlgebraIso C D) :
    e.Realized ∨ C.HasTournamentBasis

end Literature

namespace Coherent

private theorem iso_of_adjacency {n : Nat} {G H : Graph n} (f : Fin n ≃ Fin n)
    (hAdj : ∀ x y, Intertwiner.adjacency G x y = Intertwiner.adjacency H (f x) (f y)) :
    Isomorphic G H := by
  refine ⟨⟨f, f.symm, f.symm_apply_apply, f.apply_symm_apply, ?_⟩⟩
  intro x y
  have h := hAdj x y
  change G.edge x y = H.edge (f x) (f y)
  cases h₁ : G.edge x y <;> cases h₂ : H.edge (f x) (f y) <;>
    first | rfl | simp [Intertwiner.adjacency, h₁, h₂] at h

theorem iso_of_realized {n : Nat} {G H : Graph n} {e : AlgebraIso (closure G) (closure H)}
    (hAdj : e.map (Intertwiner.adjacency G) = Intertwiner.adjacency H) (realized : e.Realized) :
    Isomorphic G H := by
  obtain ⟨f, hf⟩ := realized
  apply iso_of_adjacency f
  intro x y
  simpa only [hAdj] using hf _ (adjacency_mem G) x y

/-- On any of the four orders, homogeneity is required only of the source.
The vertices may have any labelling, and no catalog representative is an input. -/
theorem isomorphic_of_homogeneous {n : Nat} (hn : n = 17 ∨ n = 20 ∨ n = 21 ∨ n = 22)
    {G H : Graph n} (hG : IsHomogeneous G) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨e, hAdj⟩ := Literature.lmr_coherentIso_of_qc q
  exact iso_of_realized hAdj (Literature.zivAv_schemeIso_realized hn hG (e.homogeneous_target hG) e)

/-- The exceptional directed schemes at 19 and 23 cannot separate ordinary
undirected graphs: their symmetric adjacency matrices are fixed. -/
theorem isomorphic_of_homogeneous_tournament_orders {n : Nat} (hn : n = 19 ∨ n = 23)
    {G H : Graph n} (hG : IsHomogeneous G) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨e, hAdj⟩ := Literature.lmr_coherentIso_of_qc q
  rcases Literature.zivAv_tournament_exceptions hn hG (e.homogeneous_target hG) e with real | ht
  · exact iso_of_realized hAdj real
  · have symm (i j : Fin n) : Intertwiner.adjacency G i j = Intertwiner.adjacency G j i := by
      unfold Intertwiner.adjacency
      rw [G.symm i j]
    have fixed := e.fixes_tournament_symmetric ht (adjacency_mem G) symm
    apply iso_of_adjacency (Equiv.refl _)
    intro x y
    exact congrFun (congrFun (fixed.symm.trans hAdj) x) y

end Coherent
end QGI
