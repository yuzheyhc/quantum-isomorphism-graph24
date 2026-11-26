import Mathlib
import GraphTypes

open scoped BigOperators

namespace QGI

abbrev Question (n : Nat) := Bool × Fin n

/-- false asks for the image of a G-vertex; true asks for the inverse image of an H-vertex.
The returned pair always has its G-end first and its H-end second. -/
def ends {n : Nat} (q : Question n) (a : Fin n) : Fin n × Fin n :=
  if q.1 then (a, q.2) else (q.2, a)

def rel {n : Nat} (G : Graph n) (x y : Fin n) : Bool × Bool :=
  (decide (x = y), G.edge x y)

/-- The assigned pair is losing if its types (equal/edge/nonedge) differ across the graphs. -/
def Loses {n : Nat} (G H : Graph n)
    (q r : Question n) (a b : Fin n) : Prop :=
  rel G (ends q a).1 (ends r b).1 ≠ rel H (ends q a).2 (ends r b).2

section Measurements

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- A projection-valued measurement, including all outcomes, on a complex Hilbert space. -/
structure IsPVM {n : Nat} (P : Fin n → (K →L[ℂ] K)) : Prop where
  selfAdjoint : ∀ a x y, @inner ℂ K _ (P a x) y = @inner ℂ K _ x (P a y)
  idempotent : ∀ a x, P a (P a x) = P a x
  orthogonal : ∀ a b, a ≠ b → ∀ x, P a (P b x) = 0
  complete : ∀ x, (∑ a : Fin n, P a x) = x

/-- Commuting-operator strategy for the ordinary two-graph isomorphism game.
For commuting projections the joint probability is ‖P Q psi‖². -/
structure PerfectStrategy {n : Nat} (G H : Graph n) (K : Type)
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] where
  psi : K
  norm_psi : ‖psi‖ = 1
  alice : Question n → Fin n → (K →L[ℂ] K)
  bob : Question n → Fin n → (K →L[ℂ] K)
  alicePVM : ∀ q, IsPVM (alice q)
  bobPVM : ∀ r, IsPVM (bob r)
  commute : ∀ q r a b x, alice q a (bob r b x) = bob r b (alice q a x)
  perfect : ∀ q r a b, Loses G H q r a b → alice q a (bob r b psi) = 0

end Measurements

/-- The Hilbert space can be infinite-dimensional. Completeness and a unit state
are required. The Hilbert carrier is a small type, with arbitrary scalar coefficients. -/
def QuantumIso {n : Nat} (G H : Graph n) : Prop :=
  ∃ (K : Type) (g : NormedAddCommGroup K),
    letI : NormedAddCommGroup K := g
    ∃ ip : InnerProductSpace ℂ K,
      letI : InnerProductSpace ℂ K := ip
      ∃ _hc : CompleteSpace K, Nonempty (PerfectStrategy G H K)

abbrev IsQcIso {n : Nat} (G H : Graph n) : Prop := QuantumIso G H

def NoSeparation (n : Nat) : Prop :=
  ∀ G H : Graph n, QuantumIso G H → Isomorphic G H

def Separation (n : Nat) : Prop :=
  ∃ G H : Graph n, QuantumIso G H ∧ ¬ Isomorphic G H

def ExactMinimum (n : Nat) : Prop :=
  Separation n ∧ ∀ m : Nat, m < n → ¬ Separation m

abbrev SixteenVertexClaim : Prop := NoSeparation 16
abbrev ExactMinimum24 : Prop := ExactMinimum 24

/-- Sufficient verifiable obligations for one order. An index i denotes a representative.
The fingerprint need only be quantum-invariant and distinguish different representatives. -/
structure CatalogCertificate (n : Nat) where
  entries : Nat
  representative : Fin entries → Graph n
  fingerprint : Graph n → List Nat
  covers : ∀ G : Graph n, ∃ i, Isomorphic G (representative i)
  respectsIso : ∀ G H, Isomorphic G H → fingerprint G = fingerprint H
  respectsQuantum : ∀ G H, QuantumIso G H → fingerprint G = fingerprint H
  distinguishes : ∀ i j,
    fingerprint (representative i) = fingerprint (representative j) → i = j

theorem noSeparation_of_certificate {n : Nat} (C : CatalogCertificate n) :
    NoSeparation n := by
  intro G H hq
  obtain ⟨i, hG⟩ := C.covers G
  obtain ⟨j, hH⟩ := C.covers H
  have same : C.fingerprint (C.representative i) = C.fingerprint (C.representative j) :=
    ((C.respectsIso G _ hG).symm.trans (C.respectsQuantum G H hq)).trans
      (C.respectsIso H _ hH)
  have hij := C.distinguishes i j same
  subst j
  obtain ⟨g⟩ := hG
  obtain ⟨h⟩ := hH
  exact ⟨g.trans h.symm⟩

/-- Concrete data sufficient for the upper bound; for the 24-vertex graph pair
obtained from the magic square the separating independent-set size is six. -/
structure UpperWitness (n : Nat) where
  G : Graph n
  H : Graph n
  K : Type
  groupK : NormedAddCommGroup K
  ipK : letI : NormedAddCommGroup K := groupK; InnerProductSpace ℂ K
  completeK : letI : NormedAddCommGroup K := groupK; CompleteSpace K
  strategy :
    letI : NormedAddCommGroup K := groupK
    letI : InnerProductSpace ℂ K := ipK
    PerfectStrategy G H K
  k : Nat
  independentG : HasIndependentSet G k
  noIndependentH : ¬ HasIndependentSet H k

theorem separation_of_witness {n : Nat} (w : UpperWitness n) : Separation n := by
  refine ⟨w.G, w.H, ?_, ?_⟩
  · exact ⟨w.K, w.groupK, w.ipK, w.completeK, ⟨w.strategy⟩⟩
  · rintro ⟨e⟩
    exact w.noIndependentH (e.mapIndependentSet w.independentG)

/-- Logical assembly. Combine lower-bound certificates with an explicit upper-bound witness. -/
theorem minimum_of_certificates {n : Nat} (upper : UpperWitness n)
    (lower : ∀ m : Nat, m < n → CatalogCertificate m) : ExactMinimum n := by
  refine ⟨separation_of_witness upper, ?_⟩
  intro m hlt sep
  obtain ⟨G, H, q, ni⟩ := sep
  exact ni (noSeparation_of_certificate (lower m hlt) G H q)

end QGI
