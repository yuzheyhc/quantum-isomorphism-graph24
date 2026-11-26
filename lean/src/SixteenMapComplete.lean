import SixteenMapSearch
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.EquivFin

namespace QGI.SixteenMapSearch

open private nextChoice searchMaps asMap tensorOK transOK atN mulC pointMap pointOK vertex
  from SixteenMapSearch

/-- The actual backtracking search used for one ordered pair by `onMatrices`. -/
def enumeratedMaps (s t : Scheme) : List (List Nat) :=
  searchMaps s t s.rank (List.range s.rank) (List.range s.rank) []

def coefficient (s : Scheme) (k i j : Nat) : Nat := mulC s k i j
def refinedKey (s : Scheme) (x : Nat) : Nat := atN s.keys x
def transposeName (s : Scheme) (x : Nat) : Nat := atN s.trans x

/-- Explicit invariants compared by the search. The function is only
constrained on actual source colors. -/
structure PreservesTests (s t : Scheme) (f : Nat → Nat) : Prop where
  range : ∀ x < s.rank, f x < s.rank
  injective : ∀ i < s.rank, ∀ j < s.rank, f i = f j → i = j
  keys : ∀ x < s.rank, refinedKey s x = refinedKey t (f x)
  transpose : ∀ i < s.rank, ∀ j < s.rank,
    transposeName s i = j ↔ transposeName t (f i) = f j
  tensor : ∀ k < s.rank, ∀ i < s.rank, ∀ j < s.rank,
    coefficient s k i j = coefficient t (f k) (f i) (f j)

private theorem pick {xs : List Nat} (options : Nat → List Nat) (ne : xs ≠ []) :
    ∃ x ∈ xs, nextChoice xs options = some (x, options x) := by
  let step (best : Option (Nat × List Nat)) (x : Nat) :=
    match best with
    | none => some (x, options x)
    | some old => if (options x).length < old.2.length then some (x, options x) else best
  let good (v : Option (Nat × List Nat)) := ∃ x ∈ xs, v = some (x, options x)
  have fold (tail : List Nat) (sub : ∀ y ∈ tail, y ∈ xs) (v) (valid : good v) :
      good (tail.foldl step v) := by
    induction tail generalizing v with
    | nil => exact valid
    | cons a l ih =>
      apply ih (fun y hy => sub y (List.mem_cons_of_mem a hy))
      obtain ⟨k, hk, rfl⟩ := valid
      unfold step
      dsimp only
      split
      · exact ⟨a, sub a (by simp), rfl⟩
      · exact ⟨k, hk, rfl⟩
  cases hx : xs with
  | nil => exact (ne hx).elim
  | cons a l =>
    have goodHead : good (some (a, options a)) := ⟨a, by simp [hx], rfl⟩
    obtain ⟨x, mem, result⟩ := fold l (fun y h => by simp [hx, h]) _ goodHead
    exact ⟨x, hx ▸ mem, result⟩

private def Correct (r : Nat) (f : Nat → Nat) (d : Assigned) : Prop :=
  ∀ a ∈ d, a.1 < r ∧ a.2 = f a.1

private theorem extendCorrect {r f d x} (hx : x < r) (h : Correct r f d) :
    Correct r f ((x,f x)::d) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | hm
  · exact ⟨hx, rfl⟩
  · exact h a hm

private theorem beq_of_iff {a b c d : Nat} (h : a = b ↔ c = d) :
    (a == b) = (c == d) := by
  by_cases eq : a = b
  · simp [eq, h.mp eq]
  · have neq : c ≠ d := fun z => eq (h.mpr z)
    simp [eq, neq]

private theorem filters_pass {s t f d x} (h : PreservesTests s t f)
    (correct : Correct s.rank f d) (hx : x < s.rank) :
    (atN s.keys x == atN t.keys (f x) && transOK s t d x (f x)) = true ∧
      tensorOK s t d x (f x) = true := by
  have prod := extendCorrect hx correct
  constructor
  · apply Bool.and_eq_true_iff.mpr
    refine ⟨beq_iff_eq.mpr (h.keys x hx), ?_⟩
    unfold transOK
    apply Bool.and_eq_true_iff.mpr
    refine ⟨beq_iff_eq.mpr (beq_of_iff (h.transpose x hx x hx)), List.all_eq_true.mpr ?_⟩
    intro a ha
    have ⟨lt,eq⟩ := correct a ha
    rw [eq]
    exact beq_iff_eq.mpr (beq_of_iff (h.transpose x hx _ lt))
  · apply List.all_eq_true.mpr
    intro a ha
    apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨al, ae⟩ := prod a ha
    obtain ⟨bl, be⟩ := prod b hb
    simp only [ae, be, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨h.tensor x hx _ al _ bl, h.tensor _ al x hx _ bl⟩, h.tensor _ al _ bl x hx⟩

private theorem totalAssigned {r f d} (correct : Correct r f d)
    (total : ∀ x < r, (x, f x) ∈ d) : asMap r d = (List.range r).map f := by
  apply List.map_congr_left
  intro x hx
  cases h : d.find? (fun a => a.1 == x) with
  | none =>
    exact False.elim ((List.find?_eq_none.mp h) (x, f x) (total x (List.mem_range.mp hx)) (by simp))
  | some v =>
    have src : v.1 = x := beq_iff_eq.mp (List.find?_some (p := fun a : Pair => a.1 == x) h)
    have dst := (correct v (List.mem_of_find?_eq_some h)).2
    simpa [src] using dst

private theorem search_complete {s t f} (h : PreservesTests s t f) (fuel : Nat)
    (pending free : List Nat) (d : Assigned) (sp : pending.length = fuel)
    (sf : free.length = fuel) (nd : pending.Nodup)
    (ok : ∀ x ∈ pending, x < s.rank ∧ f x ∈ free)
    (correct : Correct s.rank f d) (assigned : ∀ x < s.rank, x ∉ pending → (x, f x) ∈ d) :
    (List.range s.rank).map f ∈ searchMaps s t fuel pending free d := by
  induction fuel generalizing pending free d with
  | zero =>
    have ep := List.length_eq_zero_iff.mp sp
    have ef := List.length_eq_zero_iff.mp sf
    subst pending free
    simp [searchMaps, totalAssigned correct (fun x hx => assigned x hx (by simp))]
  | succ n ih =>
    let opts := fun x => free.filter fun y => atN s.keys x == atN t.keys y && transOK s t d x y
    obtain ⟨x, hx, selected⟩ := pick (xs := pending) opts (by intro e; simp [e] at sp)
    obtain ⟨xr, yr⟩ := ok x hx
    obtain ⟨filters, tensor⟩ := filters_pass h correct xr
    rw [searchMaps, selected]
    apply List.mem_flatMap.mpr
    refine ⟨f x, List.mem_filter.mpr ⟨yr, filters⟩, ?_⟩
    rw [if_pos tensor]
    apply ih
    · have := List.length_erase_add_one hx; omega
    · have := List.length_erase_add_one yr; omega
    · exact nd.erase x
    · intro u hu
      obtain ⟨different, member⟩ := nd.mem_erase_iff.mp hu
      have ⟨ur, fr⟩ := ok u member
      exact ⟨ur, (List.mem_erase_of_ne (fun eq => different (h.injective u ur x xr eq))).mpr fr⟩
    · exact extendCorrect xr correct
    · intro u ur missing
      by_cases eq : u = x
      · simp [eq]
      · exact List.mem_cons_of_mem _ (assigned u ur (fun mem => missing ((List.mem_erase_of_ne eq).mpr mem)))

/-- The actual shortest-list-first search includes every palette bijection
that preserves its tests. No step assumes the permutation was enumerated. -/
theorem mem_enumeratedMaps {s t : Scheme} {f : Nat → Nat} (h : PreservesTests s t f) :
    (List.range s.rank).map f ∈ enumeratedMaps s t := by
  unfold enumeratedMaps
  apply search_complete h s.rank _ _ _ (by simp) (by simp) List.nodup_range
  · intro x hx
    exact ⟨List.mem_range.mp hx, List.mem_range.mpr (h.range _ (List.mem_range.mp hx))⟩
  · simp [Correct]
  · intro x hx hn
    exact False.elim (hn (List.mem_range.mpr hx))

/-- A finite-palette equivalence is returned in exactly the zero-based list
format used in catalogue exception keys. The hypotheses specify the three
families of entrywise tests made on the prepared records. -/
theorem mem_of_palette_equiv (s t : Scheme) (e : Fin s.rank ≃ Fin t.rank)
    (keys : ∀ i, refinedKey s i.val = refinedKey t (e i).val)
    (tr : ∀ i j, transposeName s i.val = j.val ↔ transposeName t (e i).val = (e j).val)
    (mul : ∀ k i j, coefficient s k.val i.val j.val =
      coefficient t (e k).val (e i).val (e j).val) :
    List.ofFn (fun i => (e i).val) ∈ enumeratedMaps s t := by
  let f := fun i : Nat => if h : i < s.rank then (e ⟨i,h⟩).val else t.rank
  have rank : s.rank = t.rank := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  have hf (i : Nat) (h : i < s.rank) : f i = (e ⟨i,h⟩).val := dif_pos h
  have pr : PreservesTests s t f := {
    range := fun i hi => by rw [hf i hi]; exact lt_of_lt_of_eq (e ⟨i,hi⟩).isLt rank.symm
    injective := fun i hi j hj eq => by
      rw [hf i hi,hf j hj] at eq
      exact congrArg Fin.val (e.injective (Fin.ext eq))
    keys := fun i hi => by rw [hf i hi]; exact keys ⟨i,hi⟩
    transpose := fun i hi j hj => by rw [hf i hi,hf j hj]; exact tr ⟨i,hi⟩ ⟨j,hj⟩
    tensor := fun k hk i hi j hj => by rw [hf k hk,hf i hi,hf j hj]; exact mul ⟨k,hk⟩ ⟨i,hi⟩ ⟨j,hj⟩ }
  have entries : (List.range s.rank).map f = List.ofFn (fun i => (e i).val) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hlt : i < s.rank := by simpa using hi
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, hf i hlt]
  rw [← entries]
  exact mem_enumeratedMaps pr

end QGI.SixteenMapSearch
