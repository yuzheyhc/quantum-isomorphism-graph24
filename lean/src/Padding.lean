import QuantumGraph

/-! Padding by a new isolated vertex. The lower bound at order 23 implies
the lower bounds at all smaller orders.  -/

namespace QGI
namespace Padding

def matrix {n : Nat} (A : Fin n → Fin n → Bool)
    (i j : Fin (n+1)) : Bool :=
  Fin.cases false (fun x => Fin.cases false (A x) j) i

@[simp] theorem matrix_zero_left {n} (A : Fin n → Fin n → Bool) (j : Fin (n+1)) :
    matrix A 0 j = false := by simp [matrix]

@[simp] theorem matrix_zero_right {n} (A : Fin n → Fin n → Bool) (i : Fin (n+1)) :
    matrix A i 0 = false := by
  cases i using Fin.cases <;> simp [matrix]

@[simp] theorem matrix_succ {n} (A : Fin n → Fin n → Bool) (x y : Fin n) :
    matrix A x.succ y.succ = A x y := by simp [matrix]

def graph {n : Nat} (G : Graph n) : Graph (n+1) where
  edge := matrix G.edge
  symm := by
    intro i j
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp [G.symm]
  loopless := by
    intro i
    cases i using Fin.cases <;> simp [G.loopless]

private def flipAt {α : Type} [DecidableEq α] (a b x : α) : α :=
  if x = a then b else if x = b then a else x

private theorem flipAt_invol {α : Type} [DecidableEq α] (a b x : α) :
    flipAt a b (flipAt a b x) = x := by
  by_cases hab : a = b
  · subst b
    by_cases hx : x = a <;> simp [flipAt, hx]
  · by_cases hx : x = a
    · subst x
      simp [flipAt, hab, Ne.symm hab]
    · by_cases hy : x = b
      · subst x
        simp [flipAt, hab, Ne.symm hab]
      · simp [flipAt, hx, hy]

private def old {n : Nat} (z : Fin (n+1)) (_hz : z ≠ 0) : Fin n :=
  ⟨z.val - 1, by
    have v : z.val ≠ 0 := by
      intro h
      exact _hz (Fin.ext h)
    have w := z.isLt
    omega⟩

private theorem old_succ {n : Nat} (z : Fin (n+1)) (hz : z ≠ 0) :
    (old z hz).succ = z := by
  apply Fin.ext
  have v : z.val ≠ 0 := by
    intro h
    exact hz (Fin.ext h)
  change z.val - 1 + 1 = z.val
  omega

/-- An arbitrary isomorphism of the two padded graphs can exchange the new
vertex with an old isolated vertex. Correct it by an automorphism of the
target before restricting to the old vertices. -/
theorem cancel {n : Nat} {G H : Graph n} (e : Isomorphic (graph G) (graph H)) :
    Isomorphic G H := by
  obtain ⟨f⟩ := e
  let b := f.toFun 0
  have row (y : Fin (n+1)) : matrix H.edge b y = false := by
    have t := f.edge_eq 0 (f.invFun y)
    rw [f.rightInv] at t
    exact t.symm.trans rfl
  have col (x : Fin (n+1)) : matrix H.edge x b = false := by
    exact ((graph H).symm x b).trans (row x)
  have flipRow (x y : Fin (n+1)) :
      matrix H.edge (flipAt b 0 x) y = matrix H.edge x y := by
    by_cases hx : x = b
    · subst x
      simp [flipAt, row]
    · by_cases hz : x = 0
      · subst x
        simp [flipAt, hx, row]
      · simp [flipAt, hx, hz]
  have flipCol (x y : Fin (n+1)) :
      matrix H.edge x (flipAt b 0 y) = matrix H.edge x y := by
    by_cases hy : y = b
    · subst y
      simp [flipAt, col]
    · by_cases hz : y = 0
      · subst y
        simp [flipAt, hy, col]
      · simp [flipAt, hy, hz]
  let k : Fin (n+1) ≃ Fin (n+1) :=
    { toFun := fun x => flipAt b 0 (f.toFun x)
      invFun := fun y => f.invFun (flipAt b 0 y)
      left_inv := fun x => by
        change f.invFun (flipAt b 0 (flipAt b 0 (f.toFun x))) = x
        rw [flipAt_invol, f.leftInv]
      right_inv := fun y => by
        change flipAt b 0 (f.toFun (f.invFun (flipAt b 0 y))) = y
        rw [f.rightInv, flipAt_invol] }
  have k0 : k 0 = 0 := by
    change flipAt b 0 b = 0
    simp [flipAt]
  have k0' : k.symm 0 = 0 := by
    apply k.injective
    simp [k0]
  have kn (x : Fin n) : k x.succ ≠ 0 := by
    intro h
    exact Fin.succ_ne_zero x (k.injective (h.trans k0.symm))
  have kn' (y : Fin n) : k.symm y.succ ≠ 0 := by
    intro h
    exact Fin.succ_ne_zero y (k.symm.injective (h.trans k0'.symm))
  have ke (x y : Fin (n+1)) :
      matrix G.edge x y = matrix H.edge (k x) (k y) := by
    change matrix G.edge x y =
      matrix H.edge (flipAt b 0 (f.toFun x)) (flipAt b 0 (f.toFun y))
    rw [flipRow, flipCol]
    exact f.edge_eq x y
  let F (x : Fin n) := old (k x.succ) (kn x)
  let J (y : Fin n) := old (k.symm y.succ) (kn' y)
  have hf (x : Fin n) : (F x).succ = k x.succ := old_succ _ _
  have hj (y : Fin n) : (J y).succ = k.symm y.succ := old_succ _ _
  refine ⟨⟨F, J, ?_, ?_, ?_⟩⟩
  · intro x
    apply Fin.succ_inj.mp
    rw [hj, hf, k.symm_apply_apply]
  · intro y
    apply Fin.succ_inj.mp
    rw [hf, hj, k.apply_symm_apply]
  · intro x y
    calc
      G.edge x y = matrix G.edge x.succ y.succ := (matrix_succ _ _ _).symm
      _ = matrix H.edge (k x.succ) (k y.succ) := ke _ _
      _ = H.edge (F x) (F y) := by rw [← hf x, ← hf y, matrix_succ]

private theorem zero_ne_succ {n : Nat} (i : Fin n) : (0 : Fin (n+1)) ≠ i.succ :=
  Ne.symm (Fin.succ_ne_zero i)

attribute [local simp] zero_ne_succ Fin.succ_ne_zero

noncomputable section

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- On the new question the only possible answer is the new vertex.
On an old question the new outcome has projection zero. -/
def op {n : Nat} (P : Question n → Fin n → (K →L[ℂ] K))
    (q : Question (n+1)) (a : Fin (n+1)) : K →L[ℂ] K :=
  Fin.cases (Fin.cases (ContinuousLinearMap.id ℂ K) (fun _ => 0) a)
    (fun i => Fin.cases 0 (fun j => P (q.1, i) j) a) q.2

private theorem opPVM {n : Nat} (P : Question n → Fin n → (K →L[ℂ] K))
    (hp : ∀ q, IsPVM (P q)) (q : Question (n+1)) : IsPVM (op P q) := by
  rcases q with ⟨s,i⟩
  cases i using Fin.cases with
  | zero =>
    constructor
    · intro a x y
      cases a using Fin.cases <;> simp [op]
    · intro a x
      cases a using Fin.cases <;> simp [op]
    · intro a b h x
      cases a using Fin.cases <;> cases b using Fin.cases <;> simp_all [op]
    · intro x
      simp [Fin.sum_univ_succ, op]
  | succ i =>
    constructor
    · intro a x y
      cases a using Fin.cases <;> simp [op, (hp (s,i)).selfAdjoint]
    · intro a x
      cases a using Fin.cases <;> simp [op, (hp (s,i)).idempotent]
    · intro a b h x
      cases a using Fin.cases <;> cases b using Fin.cases <;>
        simp_all [op, (hp (s,i)).orthogonal]
    · intro x
      simpa [Fin.sum_univ_succ, op] using (hp (s,i)).complete x

set_option maxHeartbeats 3000000 in
def strategy {n : Nat} {G H : Graph n} (p : PerfectStrategy G H K) :
    PerfectStrategy (graph G) (graph H) K where
  psi := p.psi
  norm_psi := p.norm_psi
  alice := op p.alice
  bob := op p.bob
  alicePVM := opPVM p.alice p.alicePVM
  bobPVM := opPVM p.bob p.bobPVM
  commute := by
    rintro ⟨s,i⟩ ⟨t,j⟩ a b x
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      cases a using Fin.cases <;> cases b using Fin.cases <;>
      simp [op, p.commute]
  perfect := by
    rintro ⟨s,i⟩ ⟨t,j⟩ a b bad
    cases s <;> cases t <;> cases i using Fin.cases <;> cases j using Fin.cases <;>
      cases a using Fin.cases <;> cases b using Fin.cases
    all_goals try (solve | simp [op])
    all_goals try (apply False.elim; apply bad; solve | simp [rel, ends, graph, matrix])
    all_goals
      simp only [op, Fin.cases_succ, Fin.cases_zero, Prod.fst, Prod.snd]
      apply p.perfect
      simpa [Loses, rel, ends, graph, matrix] using bad

theorem quantum {n : Nat} {G H : Graph n} (h : QuantumIso G H) :
    QuantumIso (graph G) (graph H) := by
  obtain ⟨K, g, ip, hc, ⟨p⟩⟩ := h
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  exact ⟨K, g, ip, hc, ⟨strategy p⟩⟩

end

theorem promote {n : Nat} (s : Separation n) : Separation (n+1) := by
  obtain ⟨G,H,hq,hc⟩ := s
  exact ⟨graph G, graph H, quantum hq, fun e => hc (cancel e)⟩

theorem promote_le {n m : Nat} (h : n ≤ m) (s : Separation n) : Separation m := by
  induction h with
  | refl => exact s
  | step _ ih => exact promote ih

/-- A single lower boundary and one upper witness imply the entire minimum. -/
theorem exactMinimum24_iff : ExactMinimum 24 ↔ Separation 24 ∧ NoSeparation 23 := by
  classical
  constructor
  · rintro ⟨h24,low⟩
    refine ⟨h24, ?_⟩
    intro G H q
    by_contra ni
    exact low 23 (by decide) ⟨G,H,q,ni⟩
  · rintro ⟨h24,h23⟩
    refine ⟨h24, ?_⟩
    intro m hm s
    obtain ⟨G,H,q,ni⟩ := promote_le (m := 23) (by omega : m ≤ 23) s
    exact ni (h23 G H q)

end Padding
end QGI
