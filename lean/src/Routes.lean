import Lean

namespace QGI.Routes

/-- A sorted partition of total t with all parts at least l and strictly positive. -/
inductive Fits : Nat → Nat → List Nat → Prop where
  | nil (l : Nat) : Fits l 0 []
  | cons {l a t : Nat} {xs : List Nat} (la : l ≤ a) (pos : 0 < a)
      (tail : Fits a t xs) : Fits l (a+t) (a :: xs)

def enumerate : Nat → Nat → Nat → List (List Nat)
  | 0, _, t => if t = 0 then [[]] else []
  | fuel+1, l, t =>
    if t = 0 then [[]] else
      (List.range (t+1)).flatMap fun a =>
        if 0 < a ∧ l ≤ a ∧ a ≤ t then
          (enumerate fuel a (t-a)).map (a :: ·)
        else []

theorem length_le_total {l t xs} (h : Fits l t xs) : xs.length ≤ t := by
  induction h with
  | nil => simp
  | cons la pos h ih => simp only [List.length_cons]; omega

theorem complete {l t xs} (h : Fits l t xs) :
    ∀ fuel, xs.length ≤ fuel → xs ∈ enumerate fuel l t := by
  induction h with
  | nil l =>
    intro fuel _
    cases fuel <;> simp [enumerate]
  | @cons l a t xs la pos tail ih =>
    intro fuel bound
    cases fuel with
    | zero => simp at bound
    | succ f =>
      have tn : a+t ≠ 0 := by omega
      have ok : 0 < a ∧ l ≤ a ∧ a ≤ a+t := ⟨pos, la, by omega⟩
      have small : xs.length ≤ f := by simpa using bound
      have sub : a+t-a=t := by omega
      simp only [enumerate, if_neg tn, List.mem_flatMap]
      exact ⟨a, List.mem_range.mpr (by omega), by
        simpa [ok, sub] using
          (List.mem_map.mpr ⟨xs, ih f small, rfl⟩ :
            a :: xs ∈ (enumerate f a t).map (a :: ·))⟩

/-- Every enumerated list is a sorted partition of the specified total. -/
theorem enumerate_sound {fuel l t : Nat} {xs : List Nat}
    (h : xs ∈ enumerate fuel l t) : Fits l t xs := by
  induction fuel generalizing l t xs with
  | zero =>
    by_cases ht : t = 0
    · subst t
      have hx : xs = [] := by simpa [enumerate] using h
      subst xs
      exact Fits.nil l
    · simp [enumerate, ht] at h
  | succ fuel ih =>
    by_cases ht : t = 0
    · subst t
      have hx : xs = [] := by simpa [enumerate] using h
      subst xs
      exact Fits.nil l
    · simp only [enumerate, if_neg ht, List.mem_flatMap] at h
      obtain ⟨a, _, ha⟩ := h
      split at ha
      · rename_i bounds
        obtain ⟨ys, hy, rfl⟩ := List.mem_map.mp ha
        have total : a + (t - a) = t := by omega
        exact total ▸ Fits.cons bounds.2.1 bounds.1 (ih hy)
      · simp at ha

/-- The length of the enumeration counts distinct partitions. -/
theorem enumerate_nodup (fuel l t : Nat) : (enumerate fuel l t).Nodup := by
  induction fuel generalizing l t with
  | zero => by_cases ht : t = 0 <;> simp [enumerate, ht]
  | succ fuel ih =>
    by_cases ht : t = 0
    · simp [enumerate, ht]
    · rw [enumerate, if_neg ht]
      apply List.pairwise_flatMap.mpr
      constructor
      · intro a _
        split
        · apply List.pairwise_map.mpr
          exact (ih a (t - a)).imp fun h eq => h (List.cons.inj eq).2
        · exact .nil
      · apply List.nodup_range.imp
        intro a b hab x hx y hy
        split at hx <;> try contradiction
        split at hy <;> try contradiction
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
        exact fun eq => hab (List.cons.inj eq).1

/-- Starting at a part s≥4, a sweep includes every part which shares a
nontrivial divisor with a part already reached. Equal-sized fibers are
distinct entries of active; all their multiplicities are kept in sum. -/
def sweep (active seen : List Nat) : List Nat :=
  active.filter fun a => seen.any fun b => decide (1 < Nat.gcd a b)

def reach (active : List Nat) (s : Nat) : Nat → List Nat
  | 0 => [s]
  | k+1 => sweep active (reach active s k)

def maxCore (xs : List Nat) : Nat :=
  let active := xs.filter (fun a => decide (4 ≤ a))
  active.foldl (fun m a => max m (reach active a active.length).sum) 0

def hard16 : List (List Nat) :=
  [[4,4,4,4],[4,4,8],[4,6,6],[4,12],[6,10],[8,8],[16]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- A closed finite calculation over all partitions, independent of any
graph catalog. Reduction uses Lean's ordinary decide. -/
theorem computed16 :
    ((enumerate 16 1 16).filter (fun p => decide (maxCore p = 16))) = hard16 := by
  decide

theorem seven_or_smaller {xs : List Nat} (h : Fits 1 16 xs)
    (full : maxCore xs = 16) : xs ∈ hard16 := by
  rw [← computed16]
  apply List.mem_filter.mpr
  exact ⟨complete h 16 (length_le_total h), by simp [full]⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Human-readable version of the numerical calculation. -/
theorem counts16 :
    let ps := enumerate 16 1 16
    (ps.length, (ps.filter (fun p => decide (maxCore p ≤ 13))).length,
      (ps.filter (fun p => decide (maxCore p = 14))).length,
      (ps.filter (fun p => decide (maxCore p = 15))).length,
      (ps.filter (fun p => decide (maxCore p = 16))).length) = (231,210,10,4,7) := by
  decide

end QGI.Routes
