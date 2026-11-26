import HomogeneousCounts
import Mathlib

/-! Direct finite checks for Cayley graphs of the cyclic groups of orders
17, 19, 23. These computations do not read a graph or a certificate from a
catalog. For each mask the proposed multiplier is checked on all vertices and
ordered pairs, independently of the algorithm used to find it. -/
namespace QGI.PrimeCayley

open QGI.Homogeneous

def width (p : Nat) : Nat := (p-1)/2
def numMasks (p : Nat) : Nat := 2^(width p)

/-- Bit k encodes both differences k+1 and p-(k+1). The diagonal is empty. -/
def adj (p mask i j : Nat) : Nat :=
  let d := (p+j-i)%p
  if d = 0 then 0 else (mask >>> (min d (p-d)-1)) &&& 1

def graph (p mask : Nat) : QGI.Homogeneous.Graph :=
  ⟨p, (Array.range p).map fun i => (Array.range p).map fun j => adj p mask i j⟩

/-- Connection set after pulling back the old relation by multiplication by u. -/
def pullback (p mask u : Nat) : Nat :=
  (List.range (width p)).foldl (fun key i =>
    key + (adj p mask 0 ((u*(i+1))%p) <<< i)) 0

/-- Return (smallest encountered mask, multiplier from it to the input). -/
def best (p mask : Nat) : Nat × Nat := Id.run do
  let mut chosen := (mask,1)
  for u in [1:p] do
    if Nat.gcd u p == 1 then
      let r := pullback p mask u
      if r < chosen.1 then chosen := (r,u)
  return chosen

/-- The proposed multiplier defines a bijection which preserves the entire
adjacency matrix, including all nonedges. -/
def Works (p rep mask u : Nat) : Prop :=
  Nat.gcd u p = 1 ∧
  (∀ i j : Fin p, (u*i.val)%p = (u*j.val)%p → i = j) ∧
  (∀ j : Fin p, ∃ i : Fin p, (u*i.val)%p = j.val) ∧
  (∀ i j : Fin p,
    adj p rep i.val j.val = adj p mask ((u*i.val)%p) ((u*j.val)%p))

instance (p rep mask u : Nat) : Decidable (Works p rep mask u) := by
  unfold Works
  infer_instance

def routesOK (p : Nat) : Bool :=
  (List.range (numMasks p)).all fun m =>
    let chosen := best p m
    decide (Works p chosen.1 m chosen.2)

private def uniqueNats : List Nat → List Nat
  | [] => []
  | a :: xs => if a ∈ xs then uniqueNats xs else a :: uniqueNats xs

private theorem mem_uniqueNats {x : Nat} (xs : List Nat) : x ∈ uniqueNats xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [uniqueNats]
  | cons a xs ih =>
    by_cases h : a ∈ xs
    · rw [uniqueNats, if_pos h, ih]
      constructor
      · intro q; exact List.mem_cons.mpr (Or.inr q)
      · intro q
        rcases List.mem_cons.mp q with rfl | q
        · exact h
        · exact q
    · simp [uniqueNats,h,ih]

def reps (p : Nat) : List Nat :=
  uniqueNats ((List.range (numMasks p)).map fun m => (best p m).1)

/-- HomogeneousCounts.signature third coordinate: the homomorphism count
of three paths of lengths 1,3,9 with common endpoints. -/
def theta (p m : Nat) : Nat :=
  (signature (graph p m)).2.2.1

/-- Check the unprojected input-to-representative equality as a finite
calculation as well. The resulting injectivity theorem needs no imported
planar-invariance or graph-catalog lemma. -/
def consistentTheta (p : Nat) : Bool :=
  (List.range (numMasks p)).all fun m => theta p m == theta p (best p m).1

def Evidence (p expected : Nat) : Prop :=
  routesOK p = true ∧ consistentTheta p = true ∧
    (reps p).length = expected ∧ ((reps p).map (theta p)).Nodup

instance (p expected : Nat) : Decidable (Evidence p expected) := by
  unfold Evidence
  infer_instance

theorem chosen_works {p k m : Nat} (h : Evidence p k) (bound : m < numMasks p) :
    Works p (best p m).1 m (best p m).2 := by
  have t := List.all_eq_true.mp h.1 m (List.mem_range.mpr bound)
  exact of_decide_eq_true t

/-- Extract a real permutation from the numerical multiplier check. -/
theorem actualIsomorphism {p rep m u : Nat} (hp : 0 < p) (h : Works p rep m u) :
    ∃ f : Fin p ≃ Fin p, ∀ x y : Fin p,
      adj p rep x.val y.val = adj p m (f x).val (f y).val := by
  let f : Fin p → Fin p := fun x => ⟨(u*x.val)%p,Nat.mod_lt _ hp⟩
  have inj : Function.Injective f := by
    intro i j eq
    exact h.2.1 i j (congrArg Fin.val eq)
  have surj : Function.Surjective f := by
    intro j
    obtain ⟨i,eq⟩ := h.2.2.1 j
    exact ⟨i,Fin.ext eq⟩
  exact ⟨Equiv.ofBijective f ⟨inj,surj⟩,h.2.2.2⟩

private theorem memReps {p m : Nat} (hm : m < numMasks p) : (best p m).1 ∈ reps p := by
  have h : (best p m).1 ∈ ((List.range (numMasks p)).map fun t => (best p t).1) :=
    List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩
  exact (mem_uniqueNats _).mpr h

private theorem injOnList (f : Nat → Nat) {a b : Nat} (s : List Nat)
    (nd : (s.map f).Nodup) (ha : a ∈ s) (hb : b ∈ s) (eq : f a = f b) : a = b := by
  induction s with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at nd
    rcases List.mem_cons.mp ha with ha | ha <;> rcases List.mem_cons.mp hb with hb | hb
    · exact ha.trans hb.symm
    · subst a
      exact (nd.1 (List.mem_map.mpr ⟨b, hb, eq.symm⟩)).elim
    · subst b
      exact (nd.1 (List.mem_map.mpr ⟨a, ha, eq⟩)).elim
    · exact ih nd.2 ha hb

/-- For every mask, not just the selected representatives, equal theta values
imply the corresponding finite Cayley graphs are classically isomorphic. -/
theorem iso_of_same_theta {p k a b : Nat} (hyp : Evidence p k) (pos : 0 < p)
    (ha : a < numMasks p) (hb : b < numMasks p) (eq : theta p a = theta p b) :
    ∃ f : Fin p ≃ Fin p, ∀ i j : Fin p,
      adj p a i.val j.val = adj p b (f i).val (f j).val := by
  have ca := List.all_eq_true.mp hyp.2.1 a (List.mem_range.mpr ha)
  have cb := List.all_eq_true.mp hyp.2.1 b (List.mem_range.mpr hb)
  have ea : theta p a = theta p (best p a).1 := beq_iff_eq.mp ca
  have eb : theta p b = theta p (best p b).1 := beq_iff_eq.mp cb
  have repEq := injOnList (theta p) (reps p) hyp.2.2.2 (memReps ha) (memReps hb)
    (ea.symm.trans (eq.trans eb))
  obtain ⟨f,hf⟩ := actualIsomorphism pos (chosen_works hyp ha)
  obtain ⟨g,hg⟩ := actualIsomorphism pos (chosen_works hyp hb)
  rw [← repEq] at hg
  refine ⟨f.symm.trans g, ?_⟩
  intro i j
  simpa using (hf (f.symm i) (f.symm j)).symm.trans (hg (f.symm i) (f.symm j))

def runCLI (args : List String) : IO Unit := do
  let orders ← match args with
    | [] => pure [(17,36),(19,60),(23,188)]
    | ["17"] => pure [(17,36)]
    | ["19"] => pure [(19,60)]
    | ["23"] => pure [(23,188)]
    | _ => throw (IO.userError "expected 17, 19 or 23")
  for pair in orders do
    let (p,k) := pair
    if decide (Evidence p k) then
      IO.println s!"order {p}: {numMasks p} masks, {k} representatives with distinct theta counts"
    else throw (IO.userError s!"cyclic Cayley verification failed at order {p}")

end QGI.PrimeCayley
