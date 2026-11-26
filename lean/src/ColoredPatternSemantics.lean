import certificates.Witnesses

namespace QGI.Certificate

/-- Evaluate a list of directed, individually colored constraints on one full assignment. -/
def satisfies (m : ColorMatrix) (assignment : Array Nat) (arcs : List Arc) : Bool :=
  arcs.all fun e => m.get (assignment[e.tail]?.getD m.order) (assignment[e.head]?.getD m.order) == e.col

/-- The ordinary sum over all assignments of the remaining labelled variables.
Every variable independently ranges over 0,…,n−1, so repeated images are allowed. -/
def assignmentSum (n : Nat) : Nat → Array Nat → (Array Nat → Nat) → Nat
  | 0, given, f => f given
  | k+1, given, f =>
    ((List.range n).map (fun v => assignmentSum n k (given.push v) f)).sum

def partitionCount (m : ColorMatrix) (p : Pattern) (colors : List Nat) : Nat :=
  assignmentSum m.order p.order #[] fun a =>
    if (constraints p colors).all (satisfies m a) then 1 else 0

private def Prefix (a b : Array Nat) : Prop :=
  a.size ≤ b.size ∧ ∀ j, j < a.size → b[j]? = a[j]?

private theorem push_extends (a : Array Nat) (x : Nat) : Prefix a (a.push x) := by
  constructor
  · simp
  · intro j hj
    simp [Array.getElem?_push, hj, Nat.ne_of_lt hj]

private theorem assignment_congr {a : Array Nat} {f g : Array Nat → Nat} {n k : Nat}
    (h : ∀ b, Prefix a b → f b = g b) : assignmentSum n k a f = assignmentSum n k a g := by
  induction k generalizing a with
  | zero => exact h a ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | succ k ih =>
    simp only [assignmentSum]
    apply congrArg List.sum
    apply List.map_congr_left
    intro x _
    apply ih
    intro b hb
    have hpush := push_extends a x
    exact h b ⟨Nat.le_trans hpush.1 hb.1,
      fun j hj => (hb.2 j (Nat.lt_of_lt_of_le hj hpush.1)).trans (hpush.2 j hj)⟩

private theorem assignment_zero (n k : Nat) (a : Array Nat) :
    assignmentSum n k a (fun _ => 0) = 0 := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    have z (xs : List Nat) : (xs.map (fun _ : Nat => (0 : Nat))).sum = 0 := by
      induction xs with
      | nil => rfl
      | cons x xs hs => simp [hs]
    simp [assignmentSum, ih, z]

private theorem all_congr_on {α : Type} (l : List α) (f g : α → Bool)
    (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

private theorem fold_count (xs : List Nat) (passing : Nat → Bool) (weight : Nat → Nat)
    (initial : Nat) :
    xs.foldl (fun a v => if passing v then a + weight v else a) initial =
      initial + (xs.map (fun v => if passing v then weight v else 0)).sum := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
    cases h : passing x <;> simp only [List.foldl_cons, List.map_cons, List.sum_cons, h] <;>
      simp [ih, Nat.add_assoc]

private theorem countFrom_spec (m : ColorMatrix) (levels : List (List Arc)) (given : Array Nat)
    (bound : ∀ i : Fin levels.length, ∀ e ∈ levels[i.val],
        max e.tail e.head < given.size + i.val + 1) :
    countFrom m levels given = assignmentSum m.order levels.length given
      (fun a => if levels.all (satisfies m a) then 1 else 0) := by
  induction levels generalizing given with
  | nil => simp [countFrom, assignmentSum]
  | cons level rest ih =>
    simp only [countFrom, List.length_cons, assignmentSum]
    rw [fold_count, Nat.zero_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro v _
    let a := given.push v
    have nextBound (i : Fin rest.length) (e : Arc) (he : e ∈ rest[i.val]) :
        max e.tail e.head < a.size + i.val + 1 := by
      have h := bound (⟨i.val+1, by simp⟩ : Fin (level :: rest).length) e (by simpa using he)
      simpa [a, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have fixed (b : Array Nat) (hb : Prefix a b) : satisfies m b level = satisfies m a level := by
      apply all_congr_on
      intro e he
      have h := bound (⟨0,by simp⟩ : Fin (level :: rest).length) e (by simpa using he)
      change max e.tail e.head < given.size + 0 + 1 at h
      have ht : e.tail < a.size := by simp [a]; omega
      have hh : e.head < a.size := by simp [a]; omega
      rw [hb.2 e.tail ht, hb.2 e.head hh]
    change (if satisfies m a level then countFrom m rest a else 0) =
      assignmentSum m.order rest.length a (fun b => if (level :: rest).all (satisfies m b) then 1 else 0)
    cases ok : satisfies m a level with
    | true =>
      simp only [if_true]
      rw [ih a nextBound]
      exact assignment_congr fun b hb => by simp [fixed b hb, ok]
    | false =>
      simp only [Bool.false_eq_true, if_false]
      calc
        0 = assignmentSum m.order rest.length a (fun _ => 0) := (assignment_zero _ _ _).symm
        _ = _ := assignment_congr fun b hb => by simp [fixed b hb, ok]

/-- The archive's early-pruning evaluator equals the ordinary partition
function of its directed binary incidence constraints, for every color matrix. -/
theorem homCount_eq_partitionCount (m : ColorMatrix) (p : Pattern) (colors : List Nat) :
    homCount m p colors = partitionCount m p colors := by
  have len : (constraints p colors).length = p.order := by simp [constraints]
  have h := countFrom_spec m (constraints p colors) #[] (by
    intro i e he
    simp only [constraints, List.getElem_map, List.getElem_range, List.mem_filter] at he
    have eq : max e.tail e.head = i.val := of_decide_eq_true (by simpa using he.2)
    simp [eq])
  simpa only [homCount, partitionCount, len] using h

/-- Every directed test edge paired with its supplied color, in the source's
argument order. This list has no reference to the evaluation levels. -/
def paintedArcs (edges : List (Nat × Nat)) (colors : List Nat) : List Arc :=
  edges.zipWith (fun e c => ⟨e.1,e.2,c⟩) colors

def binaryCspCount (m : ColorMatrix) (p : Pattern) (colors : List Nat) : Nat :=
  assignmentSum m.order p.order #[] fun a =>
    if satisfies m a (paintedArcs p.edges colors) then 1 else 0

private theorem edge_origin {edges : List (Nat × Nat)} {colors : List Nat} {e : Arc}
    (h : e ∈ paintedArcs edges colors) : (e.tail,e.head) ∈ edges := by
  induction edges generalizing colors with
  | nil => simp [paintedArcs] at h
  | cons f fs ih =>
    cases colors with
    | nil => simp [paintedArcs] at h
    | cons c cs =>
      change e ∈ (⟨f.1,f.2,c⟩ : Arc) :: paintedArcs fs cs at h
      rcases List.mem_cons.mp h with rfl | ht
      · simp
      · exact List.mem_cons_of_mem _ (ih ht)

/-- Grouping the directed edges by their last endpoint does not change the
0-1 product of constraints at any fixed assignment. -/
private theorem levels_eq_arcs (m : ColorMatrix) (p : Pattern) (colors : List Nat) (a : Array Nat) :
    (constraints p colors).all (satisfies m a) = satisfies m a (paintedArcs p.edges colors) := by
  have valid : ∀ f ∈ p.edges, max f.1 f.2 < p.order := by cases p <;> decide
  let arcs := paintedArcs p.edges colors
  change ((List.range p.order).map (fun k => arcs.filter (fun e => max e.tail e.head == k))).all
    (satisfies m a) = satisfies m a arcs
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    apply List.all_eq_true.mpr
    intro e he
    have hk := valid _ (edge_origin he)
    have hl := List.all_eq_true.mp h _
      (List.mem_map.mpr ⟨max e.tail e.head, List.mem_range.mpr hk, rfl⟩)
    exact List.all_eq_true.mp hl e (List.mem_filter.mpr ⟨he, by simp⟩)
  · intro h
    apply List.all_eq_true.mpr
    rintro level hl
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hl
    apply List.all_eq_true.mpr
    intro e he
    exact List.all_eq_true.mp h e (List.mem_filter.mp he).1

/-- Semantic statement for the original edge list: the checker counts exactly the
assignments which satisfy the ordered binary predicate on every colored edge. -/
theorem homCount_eq_binaryCspCount (m : ColorMatrix) (p : Pattern) (colors : List Nat) :
    homCount m p colors = binaryCspCount m p colors := by
  rw [homCount_eq_partitionCount]
  unfold partitionCount binaryCspCount
  exact assignment_congr fun a _ => by rw [levels_eq_arcs]

end QGI.Certificate
