import CoprimeBlocks
import Routes

namespace QGI.Coherent.CoprimeProfiles
open Relations

/-- The size list records each actual diagonal class once, also when two
different fibers have the same size. -/
structure Profile {n : Nat} (G : Graph n) (xs : List Nat) where
  tag : Fin n → Fin xs.length
  same : ∀ i j, tag i = tag j ↔ color (closure G) i i = color (closure G) j j
  size : ∀ i, (Finset.univ.filter (fun z => tag z = i)).card = xs[i.val]

theorem Profile.fiber_size {n : Nat} {G : Graph n} {xs : List Nat} (P : Profile G xs) (i : Fin n) :
    (fiber G i).card = xs[(P.tag i).val] := by
  have eq : fiber G i = Finset.univ.filter (fun j => P.tag j = P.tag i) := by
    ext j; simp only [Finset.mem_filter,Finset.mem_univ,true_and,P.same,Relations.same,mem_fiber]
  rw [eq,P.size]

theorem Profile.occurs {n : Nat} {G : Graph n} {xs : List Nat} (P : Profile G xs)
    (j : Fin xs.length) (pos : 0 < xs[j.val]) : ∃ i, P.tag i = j := by
  obtain ⟨i,h⟩ := Finset.card_pos.mp (pos.trans_eq (P.size j).symm)
  exact ⟨i,(Finset.mem_filter.mp h).2⟩

theorem Profile.fiber_of_mem {n : Nat} {G : Graph n} {xs : List Nat} (P : Profile G xs)
    {m : Nat} (h : m ∈ xs) (pos : 0 < m) : ∃ i, (fiber G i).card = m := by
  obtain ⟨j,bound,eq⟩ := List.mem_iff_getElem.mp h
  let k : Fin xs.length := ⟨j,bound⟩
  obtain ⟨i,hi⟩ := P.occurs k (eq.symm ▸ pos)
  exact ⟨i,by rw [P.fiber_size,hi]; exact eq⟩

private def labels (minimum : Nat) (xs : List Nat) : List Nat :=
  let ids := List.range xs.length
  ids.foldl (fun groups i => ids.foldl (fun current j =>
    if minimum ≤ xs.getD i 0 ∧ minimum ≤ xs.getD j 0 ∧ 1 < (xs.getD i 0).gcd (xs.getD j 0) then
      let old := current.getD i 0
      let merged := current.getD j 0
      current.map fun a => if a = old then merged else a
    else current) groups) ids

private def mark (m : Nat) (xs : List Nat) (i : Fin xs.length) := (labels m xs).getD i.val 0
private def members (m : Nat) (xs : List Nat) (b : Nat) := Finset.univ.filter (fun i => mark m xs i = b)
private def weight (m : Nat) (xs : List Nat) (b : Nat) : Nat := ∑ i ∈ members m xs b, xs[i.val]

/-- Recheck both defining properties of the candidate partition. Correctness
of the search which produced the labels is not needed. -/
private def checkGroups (m : Nat) (xs groups : List Nat) : Bool :=
  let atIndex := fun i : Fin xs.length => groups.getD i.val 0
  let totalAt := fun b => ∑ i ∈ Finset.univ.filter (fun j => atIndex j = b), xs[i.val]
  decide ((∀ i : Fin xs.length, totalAt (atIndex i) ≤ 13) ∧
    ∀ i j : Fin xs.length, m ≤ xs[i.val] → m ≤ xs[j.val] → atIndex i ≠ atIndex j → xs[i.val].Coprime xs[j.val])

def checkFrom (m : Nat) (xs : List Nat) : Bool := checkGroups m xs (labels m xs)

def checks (xs : List Nat) : Bool := checkFrom 0 xs

theorem grouping {n : Nat} {G : Graph n} {xs : List Nat} (m : Nat)
    (shape : Profile G xs) (valid : checkFrom m xs = true) :
    ∃ b, (∀ t, CoprimeBlocks.blockSize G b t ≤ 13) ∧ ∀ i j, m ≤ (fiber G i).card →
      m ≤ (fiber G j).card → b (color (closure G) i i) ≠ b (color (closure G) j j) →
      (fiber G i).card.Coprime (fiber G j).card := by
  classical
  have data : (∀ i : Fin xs.length, weight m xs (mark m xs i) ≤ 13) ∧
      ∀ i j : Fin xs.length, m ≤ xs[i.val] → m ≤ xs[j.val] →
        mark m xs i ≠ mark m xs j → xs[i.val].Coprime xs[j.val] := of_decide_eq_true valid
  obtain ⟨sizes,apart⟩ := data
  let c := color (closure G)
  let b := fun v => if h : ∃ i, c i i = v then mark m xs (shape.tag h.choose) else 0
  have atPoint (i : Fin n) : b (c i i) = mark m xs (shape.tag i) := by
    let h : ∃ j, c j j = c i i := ⟨i,rfl⟩
    simp only [b,dif_pos h]
    exact congrArg _ ((shape.same _ _).mpr h.choose_spec)
  refine ⟨b,?_,?_⟩
  · intro t
    have eq := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n)) (members m xs t) shape.tag
    simp only [shape.size] at eq
    have value : CoprimeBlocks.blockSize G b t = weight m xs t := by
      change (Finset.univ.filter (fun i => b (c i i) = t)).card = _
      simp_rw [atPoint]
      simpa only [weight,members,Finset.mem_filter,Finset.mem_univ,true_and] using eq.symm
    rw [value]
    by_cases occurs : ∃ i, mark m xs i = t
    · obtain ⟨i,rfl⟩ := occurs; exact sizes i
    · push_neg at occurs
      simp [weight,members,occurs]
  · intro i j hi hj diff
    rw [shape.fiber_size] at hi hj
    rw [shape.fiber_size,shape.fiber_size]
    exact apart _ _ hi hj (fun eq => diff ((atPoint i).trans (eq.trans (atPoint j).symm)))

theorem isomorphic_of_profile {n : Nat} {G H : Graph n} {xs : List Nat}
    (shape : Profile G xs) (valid : checks xs = true) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨b,small,apart⟩ := grouping 0 shape valid
  exact CoprimeBlocks.isomorphic_of_small_blocks b small (fun i j => apart i j (Nat.zero_le _) (Nat.zero_le _)) q

def total (n : Nat) : Nat × Nat :=
  let profiles := Routes.enumerate n 1 n
  (profiles.length,(profiles.filter checks).length)

set_option maxRecDepth 10000 in
theorem counted : (List.range 8).map (fun i => total (16+i)) =
    [(231,178),(297,220),(385,264),(490,315),(627,371),(792,432),(1002,506),(1255,579)] := by
  native_decide

end QGI.Coherent.CoprimeProfiles
