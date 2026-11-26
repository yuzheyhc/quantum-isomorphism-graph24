import QuantumCounts
import PrimeCayley

/-! A sound, executable Nat version of the two-terminal count. Each matrix
product is tabulated once, so evaluating a certificate never expands all
length-nine walks. Coordinates may use an arbitrary permutation of Fin n. -/

open scoped BigOperators

namespace QGI.ThetaBridge

open QGI.Intertwiner

abbrev NMat (n : Nat) := Vector (Vector Nat n) n

def tab {n : Nat} (a : Fin n → Fin n → Nat) : NMat n :=
  Vector.ofFn fun i => Vector.ofFn fun j => a i j

def entry {n : Nat} (a : NMat n) (i j : Fin n) : Nat := a[i.val][j.val]

@[simp] theorem entry_tab {n : Nat} (a : Fin n → Fin n → Nat) (i j : Fin n) :
    entry (tab a) i j = a i j := by
  simp [entry, tab]

def prod {n : Nat} (a b : NMat n) : NMat n :=
  tab fun i j => ∑ k : Fin n, entry a i k * entry b k j

def thetaNat {n : Nat} (a : NMat n) : Nat :=
  let a2 := prod a a
  let a3 := prod a2 a
  let a6 := prod a3 a3
  let a9 := prod a6 a3
  ∑ i : Fin n, ∑ j : Fin n, entry a i j * (entry a3 i j * entry a9 i j)

/-- The integer table is the complex matrix expressed using coordinates e. -/
def Reads {n : Nat} (e : Fin n ≃ Fin n) (a : NMat n) (A : Mat n) : Prop :=
  ∀ i j, (entry a i j : ℂ) = A (e i) (e j)

theorem reads_prod {n : Nat} {e : Fin n ≃ Fin n} {a b : NMat n} {A B : Mat n}
    (ha : Reads e a A) (hb : Reads e b B) : Reads e (prod a b) (A * B) := by
  intro i j
  unfold Reads at ha hb
  simp only [prod, entry_tab, Nat.cast_sum, Nat.cast_mul, ha, hb, Matrix.mul_apply]
  exact Equiv.sum_comp e (fun k => A (e i) k * B k (e j))

/-- All integer computations and all relabelings used below satisfy this one
identity. It is valid in every order and requires no graph transitivity. -/
theorem thetaNat_spec {n : Nat} {e : Fin n ≃ Fin n} {a : NMat n} {G : Graph n}
    (ha : Reads e a (adjacency G)) : (thetaNat a : ℂ) = theta139Count G := by
  have h2 : Reads e (prod a a) (walk2 G) := reads_prod ha ha
  have h3 : Reads e (prod (prod a a) a) (walk3 G) := reads_prod h2 ha
  have h6 := reads_prod h3 h3
  have h9 : Reads e (prod (prod (prod (prod a a) a) (prod (prod a a) a))
      (prod (prod a a) a)) (walk9 G) := reads_prod h6 h3
  unfold Reads at ha h3 h9
  unfold thetaNat theta139Count total
  simp only [Nat.cast_sum, Nat.cast_mul, ha, h3, h9]
  let z := fun i j => adjacency G i j * (walk3 G i j * walk9 G i j)
  change (∑ i : Fin n, ∑ j : Fin n, z (e i) (e j)) = ∑ i : Fin n, ∑ j : Fin n, z i j
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n, z (e i) j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp e (z (e i))
    _ = _ := Equiv.sum_comp e (fun i => ∑ j : Fin n, z i j)

/-- A cyclic labeling specifies both directions of a permutation and checks
its adjacency formula for every ordered pair. This also covers arbitrary
vertex names or arbitrary labelings on Fin p. -/
structure CyclicLabeling {p : Nat} (G : Graph p) where
  mask : Fin (PrimeCayley.numMasks p)
  label : Fin p ≃ Fin p
  edges : ∀ i j, G.edge (label i) (label j) =
    decide (PrimeCayley.adj p mask.val i.val j.val = 1)

def maskMat (p m : Nat) : NMat p :=
  tab fun i j => if PrimeCayley.adj p m i.val j.val = 1 then 1 else 0

theorem reads_mask {p : Nat} {G : Graph p} (g : CyclicLabeling G) :
    Reads g.label (maskMat p g.mask.val) (adjacency G) := by
  intro i j
  by_cases h : PrimeCayley.adj p g.mask.val i.val j.val = 1 <;>
    simp [maskMat, adjacency, g.edges, h]

/-- An independently recomputed equality with the imperative array signature,
on the complete finite input domain, including every nonrepresentative. -/
def agrees (p : Nat) : Bool :=
  (List.range (PrimeCayley.numMasks p)).all fun m =>
    thetaNat (maskMat p m) == PrimeCayley.theta p m

private theorem agrees_at {p : Nat} (ok : agrees p = true)
    (m : Fin (PrimeCayley.numMasks p)) :
    thetaNat (maskMat p m.val) = PrimeCayley.theta p m.val := by
  have t := List.all_eq_true.mp ok m.val (List.mem_range.mpr m.isLt)
  exact beq_iff_eq.mp t

/-- No extra analytic or catalog hypothesis: the two inputs supply their
coordinate systems. The finite checks for each supported order specialize
this theorem in data/homogeneous/theta/Check{17,19,23}. -/
theorem cyclicIso {p k : Nat} {G H : Graph p} (gp : CyclicLabeling G)
    (hp : CyclicLabeling H) (pos : 0 < p) (ev : PrimeCayley.Evidence p k)
    (ok : agrees p = true) (q : QuantumIso G H) : Isomorphic G H := by
  have heq : (thetaNat (maskMat p gp.mask.val) : ℂ) =
      (thetaNat (maskMat p hp.mask.val) : ℂ) :=
    (thetaNat_spec (reads_mask gp)).trans
      ((theta139_qc q).trans (thetaNat_spec (reads_mask hp)).symm)
  have heqNat : thetaNat (maskMat p gp.mask.val) = thetaNat (maskMat p hp.mask.val) := by
    exact_mod_cast heq
  have hsig := (agrees_at ok gp.mask).symm.trans (heqNat.trans (agrees_at ok hp.mask))
  obtain ⟨f,hf⟩ := PrimeCayley.iso_of_same_theta ev pos gp.mask.isLt hp.mask.isLt hsig
  let u := gp.label.symm.trans (f.trans hp.label)
  refine ⟨⟨u, u.symm, u.symm_apply_apply, u.apply_symm_apply, ?_⟩⟩
  intro x y
  let i := gp.label.symm x
  let j := gp.label.symm y
  have hb := congrArg (fun t : Nat => decide (t = 1)) (hf i j)
  simpa [u, i, j] using (gp.edges i j).trans (hb.trans (hp.edges (f i) (f j)).symm)

end QGI.ThetaBridge
