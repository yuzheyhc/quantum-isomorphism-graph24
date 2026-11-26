import DoubleEightBareLaws

namespace QGI.DoubleEight.ColumnProfiles

open ShoreCensus (V Coloring Homogeneous side)
open BareLaws (rowHistogram)
open Finset
open scoped BigOperators

def profiles : List (List Nat) := [[2,6],[3,5],[4,4],[2,2,4],[2,3,3],[2,2,2,2]]

/-- The same dense color index is used by both ends. The old color name can
be recovered from its index, and its row and column valencies equal the
corresponding entry of the sorted profile. -/
def Presentation (c : Coloring) (ds : List Nat) : Prop :=
  ∃ (name : Fin ds.length → Nat) (index : V → V → Fin ds.length),
    Function.Injective name ∧ (∀ x y, name (index x y) = c x y) ∧
      ∀ s : Fin ds.length,
        (∀ x, ((univ : Finset V).filter (fun y => index x y = s)).card = ds.get s) ∧
        (∀ y, ((univ : Finset V).filter (fun x => index x y = s)).card = ds.get s)

private theorem possibilities (ds : List Nat) (mixed : 2 ≤ ds.length)
    (small : ∀ n ∈ ds, 2 ≤ n) (sorted : ds.Pairwise (· ≤ ·)) (sum : ds.sum = 8) :
    ds ∈ profiles := by
  match ds with
  | [] | [_] => simp_all
  | [a,b] | [a,b,c] | [a,b,c,d] =>
    simp_all [profiles, List.pairwise_cons]
    omega
  | a::b::c::d::e::tail =>
    have ha := small a (by simp)
    have hb := small b (by simp)
    have hc := small c (by simp)
    have hd := small d (by simp)
    have he := small e (by simp)
    simp only [List.sum_cons] at sum
    omega

/-- With a positive lower bound of two, the six displayed profiles exhaust
every nonconstant biregular coloring with completely arbitrary color names. -/
theorem normalize (c : Coloring) (regular : FiberRectangles.BiregularColors c)
    (mixed : ∃ i j x y, c i j ≠ c x y)
    (least : ∀ i j, 2 ≤ rowHistogram c (c i j) 0) :
    ∃ ds ∈ profiles, Presentation c ds := by
  classical
  let palette := (univ : Finset (V × V)).image fun p => c p.1 p.2
  let deg := fun t => rowHistogram c t 0
  let le := fun a b => decide (deg a ≤ deg b)
  let labels := palette.toList.mergeSort le
  let ds := labels.map deg
  have listed (t : Nat) : t ∈ labels ↔ t ∈ palette := by
    simp [labels]
  have nodup : labels.Nodup := (List.mergeSort_perm palette.toList le).nodup_iff.mpr
    palette.nodup_toList
  have present (i j : V) : c i j ∈ palette := mem_image.mpr ⟨(i,j),mem_univ _,rfl⟩
  have min (t) (ht : t ∈ palette) : 2 ≤ deg t := by
    obtain ⟨⟨i,j⟩,_,rfl⟩ := mem_image.mp ht
    exact least i j
  have sorted : ds.Pairwise (· ≤ ·) := by
    apply List.pairwise_map.mpr
    simpa only [le, decide_eq_true_eq] using
      (List.sorted_mergeSort (le := le)
        (fun a b d h₁ h₂ => decide_eq_true (le_trans (of_decide_eq_true h₁) (of_decide_eq_true h₂)))
        (fun a b => Bool.or_eq_true_iff.mpr ((le_total (deg a) (deg b)).imp decide_eq_true decide_eq_true))
        palette.toList)
  have total : ds.sum = 8 := by
    have set : labels.toFinset = palette := by ext t; simpa using listed t
    rw [show ds = labels.map deg from rfl, ← List.sum_toFinset _ nodup, set]
    calc
      _ = ∑ t ∈ palette, ∑ j : V, (if c 0 j = t then 1 else 0 : Nat) := rfl
      _ = _ := by rw [Finset.sum_comm]; simp [Finset.sum_ite_eq, present]
  have len : 2 ≤ ds.length := by
    obtain ⟨i,j,x,y,h⟩ := mixed
    have h₁ := (listed _).mpr (present i j)
    have h₂ := (listed _).mpr (present x y)
    change 2 ≤ (labels.map deg).length
    rw [List.length_map]
    have two {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
        2 ≤ l.length := by
      cases l with
      | nil => simp at ha
      | cons v tail =>
        cases tail with
        | nil => simp only [List.mem_singleton] at ha hb; exact (hne (ha.trans hb.symm)).elim
        | cons w tail => simp
    exact two h₁ h₂ h
  refine ⟨ds, possibilities ds len ?_ sorted total, ?_⟩
  · intro n hn
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hn
    exact min t ((listed t).mp ht)
  have lengths : ds.length = labels.length := List.length_map deg
  let name := fun s : Fin ds.length => labels.get (Fin.cast lengths s)
  have inject : Function.Injective name := by
    intro s t h
    exact Fin.ext (congrArg (fun u : Fin labels.length => u.val) (nodup.get_inj_iff.mp h))
  have hit (i j : V) : ∃ s, name s = c i j := by
    obtain ⟨k,hk⟩ := List.mem_iff_get.mp ((listed _).mpr (present i j))
    exact ⟨k.cast lengths.symm, hk⟩
  let index := fun i j => (hit i j).choose
  have names (i j : V) : name (index i j) = c i j := (hit i j).choose_spec
  have iffColor (i j : V) (s : Fin ds.length) : index i j = s ↔ c i j = name s := by
    rw [← names i j, inject.eq_iff]
  refine ⟨name,index,inject,names,fun s => ?_⟩
  have dsGet : ds.get s = deg (name s) := by simp [ds,name,List.get_eq_getElem]
  obtain ⟨r,t,hr,ht⟩ := regular (name s)
  have same : r = t := by
    have e := FiberRectangles.balance (fun i j => decide (c i j = name s)) hr ht
    omega
  have base : deg (name s) = r := by
    simpa [deg,rowHistogram,FiberRectangles.degree] using hr 0
  rw [dsGet,base]
  constructor
  · intro x
    simpa [iffColor,FiberRectangles.degree] using hr x
  · intro y
    rw [same]
    simpa [iffColor,FiberRectangles.degree] using ht y

theorem raw_profiles (m : V ⊕ V → V ⊕ V → Nat)
    (hl : Homogeneous (fun i j => m (.inl i) (.inl j)))
    (hr : Homogeneous (fun i j => m (.inr i) (.inr j)))
    (rectangle : ∀ i j x y, m i j = m x y → (side i, side j) = (side x, side y))
    (rev : ∀ i j x y, m i j = m x y → m j i = m y x)
    (products : FixedInterface.HasIntersectionNumbers m)
    (mixed : ∃ i j x y, m (.inl i) (.inr j) ≠ m (.inl x) (.inr y))
    (least : ∀ i j, 2 ≤ rowHistogram (fun x y => m (.inl x) (.inr y)) (m (.inl i) (.inr j)) 0) :
    ∃ ds ∈ profiles, Presentation (fun i j => m (.inl i) (.inr j)) ds :=
  normalize _ (BareLaws.raw_necessary m hl hr rectangle rev products).1 mixed least

end QGI.DoubleEight.ColumnProfiles
