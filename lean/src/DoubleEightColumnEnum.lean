import Lean

namespace QGI.DoubleEight.ColumnEnum

abbrev Shore := Array Nat
abbrev Profile := List Nat
abbrev Signature := Array Nat

def profiles : Array Profile := #[[2,6], [3,5], [4,4], [2,2,4], [2,3,3], [2,2,2,2]]

/-- The eight color entries of a column are base-four digits, row zero first. -/
def letter (c i : Nat) : Nat := (c >>> (2*(7-i))) % 4

def rank (S : Shore) : Nat := S.foldl max 0 + 1

def relation (S : Shore) (i j : Nat) : Nat := S.getD (8*i+j) 255

def valency (S : Shore) (r : Nat) : Nat :=
  (List.range 8).countP fun j => relation S 0 j == r

def neighbor (S : Shore) (c r i t : Nat) : Nat :=
  (List.range 8).countP fun j => relation S i j == r && letter c j == t

def firstPoint (c s : Nat) : Nat :=
  ((List.range 8).find? fun i => letter c i == s).getD 0

def columnProfile (ds : Profile) (c : Nat) : Prop :=
  (∀ i : Fin 8, letter c i.val < ds.length) ∧
  ∀ s : Fin ds.length, (List.range 8).countP (fun i => letter c i == s.val) = ds[s.val]!

instance (ds : Profile) (c : Nat) : Decidable (columnProfile ds c) := by
  unfold columnProfile; infer_instance

def columnPool (ds : Profile) : List Nat :=
  (List.range 65536).filter fun c => decide (columnProfile ds c)

def pack (r k : Nat) (f : Nat → Nat → Nat → Nat) : Signature :=
  (Array.range (r*k*k)).map fun p => f (p/(k*k)) ((p/k)%k) (p%k)

def signature (S : Shore) (ds : Profile) (c : Nat) : Signature :=
  pack (rank S) ds.length (fun r s t => neighbor S c r (firstPoint c s) t)

def entry (q : Signature) (k r s t : Nat) : Nat := q.getD ((r*k+s)*k+t) 255

def Equitable (S : Shore) (ds : Profile) (c : Nat) (q : Signature) : Prop :=
  ∀ r : Fin (rank S), ∀ i : Fin 8, ∀ t : Fin ds.length,
    neighbor S c r.val i.val t.val = entry q ds.length r.val (letter c i.val) t.val

def Integral (S : Shore) (ds : Profile) (q : Signature) : Prop :=
  ∀ r : Fin (rank S), ∀ s t : Fin ds.length,
    (ds[s.val]! * entry q ds.length r.val s.val t.val) % valency S r.val = 0

instance (S ds c q) : Decidable (Equitable S ds c q) := by unfold Equitable; infer_instance
instance (S ds q) : Decidable (Integral S ds q) := by unfold Integral; infer_instance

def target (S : Shore) (ds : Profile) (q : Signature) (i j s t : Nat) : Nat :=
  let r := relation S i j
  ds[s]! * entry q ds.length r s t / valency S r

def gram (cols : List Nat) (i j s t : Nat) : Nat :=
  cols.countP fun c => letter c i == s && letter c j == t

private def active (S : Shore) (ds : Profile) (pool : List Nat) : List (Nat × Signature) :=
  pool.filterMap fun c =>
    let q := signature S ds c
    if Equitable S ds c q ∧ Integral S ds q then some (c, q) else none

private def keys : List (Nat × Signature) → List Signature
  | [] => []
  | (_,q) :: rest => let k := keys rest; if q ∈ k then k else q :: k

private theorem mem_keys {l : List (Nat × Signature)} {c q} (h : (c,q) ∈ l) : q ∈ keys l := by
  induction l with
  | nil => simp at h
  | cons p tail ih =>
    obtain ⟨a,b⟩ := p
    simp only [keys]
    rcases List.mem_cons.mp h with hp | ht
    · cases hp
      split <;> simp_all
    · have old := ih ht
      split <;> simp_all

private structure Test where
  i : Nat
  j : Nat
  s : Nat
  t : Nat
  limit : Nat

private structure Choice where
  code : Nat
  tests : List Test

private def choice (S : Shore) (ds : Profile) (q : Signature) (c : Nat) : Choice :=
  ⟨c, (List.finRange 8).flatMap fun i => (List.finRange 8).filterMap fun j =>
    if i ≤ j then some ⟨i.val,j.val,letter c i.val,letter c j.val,
      target S ds q i.val j.val (letter c i.val) (letter c j.val)⟩ else none⟩

private def feasible (pre : List Nat) (c : Choice) : Bool :=
  c.tests.all fun a => gram pre a.i a.j a.s a.t < a.limit

private def extend (pool : List Choice) : Nat → Nat → List Nat → List (List Nat)
  | 0, _, pre => [pre]
  | n+1, lo, pre => pool.flatMap fun c =>
    if lo ≤ c.code && feasible pre c then extend pool n c.code (pre ++ [c.code]) else []

def enumerateWith (S : Shore) (ds : Profile) (columns : List Nat) : List (List Nat) :=
  let a := active S ds columns
  (keys a).flatMap fun q =>
    let pool := a.filterMap fun (c,k) => if k=q then some (choice S ds q c) else none
    extend pool 8 0 []

/-- All sorted eight-column lists consistent with the shore relation products
and forced Gram bounds. Color renaming and left point normalization occur before this step. -/
def enumerate (S : Shore) (ds : Profile) : List (List Nat) :=
  enumerateWith S ds (columnPool ds)

/-- The point-count hypotheses sufficient for the concrete search. The Gram
bound is only used for i ≤ j, and equality also suffices. -/
structure Admissible (S : Shore) (ds : Profile) (q : Signature) (cols : List Nat) : Prop where
  size : cols.length = 8
  ordered : cols.Pairwise (· ≤ ·)
  bounded : ∀ c ∈ cols, c < 65536
  profile : ∀ c ∈ cols, columnProfile ds c
  shared : ∀ c ∈ cols, signature S ds c = q
  equitable : ∀ c ∈ cols, Equitable S ds c q
  integral : Integral S ds q
  gram_le : ∀ i j : Fin 8, i ≤ j → ∀ s t : Fin ds.length,
    gram cols i.val j.val s.val t.val ≤ target S ds q i.val j.val s.val t.val

private theorem feasible_of_admissible {S ds q cols} (h : Admissible S ds q cols)
    {pre post : List Nat} {c : Nat} (eqn : cols = pre ++ c :: post) :
    feasible pre (choice S ds q c) = true := by
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp ha
  obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hi
  split at hj
  · rename_i hij
    cases hj
    have hc : c ∈ cols := by simp [eqn]
    let s : Fin ds.length := ⟨letter c i.val, (h.profile c hc).1 i⟩
    let t : Fin ds.length := ⟨letter c j.val, (h.profile c hc).1 j⟩
    have upper := h.gram_le i j hij s t
    have sum : gram cols i.val j.val s.val t.val =
        gram pre i.val j.val s.val t.val + (1 + gram post i.val j.val s.val t.val) := by
      simp [gram, eqn, s, t, Nat.add_comm]
    change decide (gram pre i.val j.val s.val t.val < target S ds q i.val j.val s.val t.val) = true
    exact decide_eq_true (by omega)
  · cases hj

private theorem extend_complete {S ds q cols} (h : Admissible S ds q cols) {pool : List Choice}
    (present : ∀ c ∈ cols, choice S ds q c ∈ pool) (tail pre : List Nat) (lo : Nat)
    (eqn : cols = pre ++ tail) (lower : ∀ c ∈ tail, lo ≤ c) :
    cols ∈ extend pool tail.length lo pre := by
  induction tail generalizing pre lo with
  | nil => simpa [extend] using eqn
  | cons c rest ih =>
    apply List.mem_flatMap.mpr
    refine ⟨choice S ds q c, present c (by simp [eqn]), ?_⟩
    have valid := feasible_of_admissible h eqn
    have lo_ok := lower c (by simp)
    have later : ∀ x ∈ rest, c ≤ x :=
      (List.pairwise_cons.mp (List.pairwise_append.mp (eqn ▸ h.ordered)).2.1).1
    change cols ∈ (if decide (lo ≤ c) && feasible pre (choice S ds q c)
      then extend pool rest.length c (pre ++ [c]) else [])
    simpa only [decide_eq_true lo_ok, Bool.true_and, valid, if_true] using
      ih (pre ++ [c]) c (by simpa using eqn) later

/-- Every arbitrary list satisfying the intersection-number constraints is a
member of the actual search output. This theorem has no finite-computation assumption. -/
theorem mem_enumerate {S ds q cols} (h : Admissible S ds q cols) :
    cols ∈ enumerate S ds := by
  let a := active S ds (columnPool ds)
  have ha (c : Nat) (hc : c ∈ cols) : (c,q) ∈ a := by
    apply List.mem_filterMap.mpr
    refine ⟨c, List.mem_filter.mpr ⟨List.mem_range.mpr (h.bounded c hc), decide_eq_true (h.profile c hc)⟩, ?_⟩
    simp [h.shared c hc, h.equitable c hc, h.integral]
  have somec : ∃ c, c ∈ cols := by
    cases eqn : cols with
    | nil => have n := h.size; simp [eqn] at n
    | cons c cs => exact ⟨c, by simp⟩
  obtain ⟨c,hc⟩ := somec
  apply List.mem_flatMap.mpr
  refine ⟨q, mem_keys (ha c hc), ?_⟩
  let pool := a.filterMap fun (c,k) => if k=q then some (choice S ds q c) else none
  have present (z : Nat) (hz : z ∈ cols) : choice S ds q z ∈ pool := by
    exact List.mem_filterMap.mpr ⟨(z,q), ha z hz, by simp⟩
  simpa only [h.size] using extend_complete h present cols [] 0 (by simp) (by simp)

end QGI.DoubleEight.ColumnEnum
