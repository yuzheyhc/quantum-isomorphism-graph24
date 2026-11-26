import SixteenPointSound

namespace QGI.SixteenMapSearch

open private searchMaps pointMap from SixteenMapSearch

/-- The validator and the one-based numerical labels used by the original census. -/
def preparedSchemes (shape : List Nat) (data : List (Array Nat)) : Option (List Scheme) :=
  ((List.range data.length).zip data).mapM (fun im => prepare shape (im.1+1) im.2)

private def addMap (s t : Scheme) (a : Counts) (pi : List Nat) : Counts :=
  if pointTest s t pi then { a with algebraic := a.algebraic+1, geometric := a.geometric+1 }
  else { a with algebraic := a.algebraic+1, exceptions := (s.id,t.id,pi)::a.exceptions }

private def addPair (a : Counts) (s t : Scheme) : Counts :=
  if s.rank == t.rank && s.profile == t.profile then
    let a := {a with orderedPairs := a.orderedPairs + 1}
    let maps := enumeratedMaps s t
    if !maps.isEmpty then maps.foldl (addMap s t) {a with algebraicPairs := a.algebraicPairs+1}
    else maps.foldl (addMap s t) a
  else a

private theorem forIn_fold {α β : Type} {xs : List α} {init : β}
    {step : α → β → Id (ForInStep β)} {g : β → α → β}
    (eq : ∀ x b, step x b = .yield (g b x)) : forIn xs init step = xs.foldl g init := by
  rw [show step = (fun x b => ForInStep.yield (g b x)) from funext (fun x => funext (eq x))]
  exact List.forIn_yield_eq_foldl _ _

private theorem run_eq {shape data schemes} (q : preparedSchemes shape data = some schemes) :
    onMatrices shape data = some (schemes.foldl (fun a s => schemes.foldl (fun b t => addPair b s t) a) {}) := by
  change (preparedSchemes shape data >>= _) = _
  rw [q]
  simp only [Option.bind_eq_bind, Option.some_bind, Id.bind_eq, Id.pure_eq, Id.run]
  apply congrArg some
  apply forIn_fold
  intro s a
  apply congrArg ForInStep.yield
  apply forIn_fold
  intro t b
  by_cases ok : (s.rank == t.rank && s.profile == t.profile) = true
  · by_cases notEmpty : (!(enumeratedMaps s t).isEmpty) = true
    all_goals
      simp only [addPair,ok,if_true,show searchMaps s t s.rank (List.range s.rank) (List.range s.rank) [] = enumeratedMaps s t from rfl,
        notEmpty,if_false]
      apply congrArg ForInStep.yield
      apply forIn_fold
      intro pi z
      change (if pointTest s t pi then ForInStep.yield _ else ForInStep.yield _) = ForInStep.yield (addMap s t z pi)
      cases hit : pointTest s t pi <;> simp [addMap,hit]
  · simp only [addPair,ok,Bool.false_eq_true,if_false]

/-- A fold that retains all prior keys and adds exactly the keys permitted
at a step has the corresponding membership characterization after any list. -/
private theorem fold_keys {α : Type} (step : Counts → α → Counts) (P : α → Prop) (k : Key)
    (spec : ∀ a x, k ∈ (step a x).exceptions ↔ k ∈ a.exceptions ∨ P x)
    (xs : List α) (a : Counts) :
    k ∈ (xs.foldl step a).exceptions ↔ k ∈ a.exceptions ∨ ∃ x ∈ xs, P x := by
  induction xs generalizing a with
  | nil => simp
  | cons x tail ih =>
    simp only [List.foldl_cons,ih,spec,List.mem_cons,exists_eq_or_imp,or_assoc]

def AtPair (s t : Scheme) (k : Key) : Prop :=
  s.rank = t.rank ∧ s.profile = t.profile ∧
    ∃ pi ∈ enumeratedMaps s t, pointTest s t pi = false ∧ k = (s.id,t.id,pi)

private theorem addPair_keys (s t : Scheme) (k : Key) (a : Counts) :
    k ∈ (addPair a s t).exceptions ↔ k ∈ a.exceptions ∨ AtPair s t k := by
  have spec (b : Counts) (pi : List Nat) :
      k ∈ (addMap s t b pi).exceptions ↔ k ∈ b.exceptions ∨ pointTest s t pi = false ∧ k = (s.id,t.id,pi) := by
    cases hit : pointTest s t pi <;> simp [addMap,hit,or_comm]
  unfold addPair AtPair
  by_cases valid : s.rank = t.rank ∧ s.profile = t.profile
  · simp only [valid.1, valid.2, beq_self_eq_true, Bool.and_self, if_true, true_and]
    split <;> exact fold_keys _ _ k spec _ _
  · have failed : (s.rank == t.rank && s.profile == t.profile) = false := by simpa using valid
    simp only [failed, Bool.false_eq_true, if_false]
    exact ⟨Or.inl,fun h => h.resolve_right (fun n => valid ⟨n.1,n.2.1⟩)⟩

/-- Every exception recorded by the executable is exactly a failed point
test in some visited ordered pair, including the labels of both input tables. -/
theorem exceptions_iff {shape data schemes C} (prepared : preparedSchemes shape data = some schemes)
    (counted : onMatrices shape data = some C) (k : Key) :
    k ∈ C.exceptions ↔ ∃ s ∈ schemes, ∃ t ∈ schemes, AtPair s t k := by
  rw [run_eq prepared] at counted
  cases Option.some.inj counted
  have inner (a : Counts) (s : Scheme) := fold_keys (fun b t => addPair b s t)
    (fun t => AtPair s t k) k (fun b t => addPair_keys s t k b) schemes a
  simpa using fold_keys _ _ k inner schemes ({} : Counts)

/-- A particular algebraic palette map rejected by the geometric test has
its one-based source/target labels and its exact permutation in the accumulated list. -/
theorem key_mem_exceptions {shape data schemes C}
    (prepared : preparedSchemes shape data = some schemes) (counted : onMatrices shape data = some C)
    {s t : Scheme} (hs : s ∈ schemes) (ht : t ∈ schemes) (hr : s.rank = t.rank)
    (hp : s.profile = t.profile) {pi : List Nat} (hm : pi ∈ enumeratedMaps s t)
    (failed : pointTest s t pi = false) :
    (s.id,t.id,pi) ∈ C.exceptions :=
  (exceptions_iff prepared counted _).2 ⟨s,hs,t,ht,hr,hp,pi,hm,failed,rfl⟩

end QGI.SixteenMapSearch