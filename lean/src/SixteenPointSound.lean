import SixteenMapComplete
import Mathlib.Data.List.Nodup

namespace QGI.SixteenMapSearch

open private pointMap pointOK nextChoice atN vertex from SixteenMapSearch
open private pick from SixteenMapComplete

/-- Numerical entries of the table read by the catalog point search. -/
def pointColor (s : Scheme) (i j : Fin 16) : Nat := vertex s.colors i.val j.val

/-- The geometric test used by the actual census, with both vertex domains
initialized to the sixteen vertex labels. -/
def pointTest (s t : Scheme) (pi : List Nat) : Bool :=
  pointMap s t pi.toArray 16 (List.range 16) (List.range 16) []

private def ValidPairs (s t : Scheme) (pi : Array Nat) (d : Assigned) : Prop :=
  ∀ a ∈ d, ∀ b ∈ d, atN pi (vertex s.colors a.1 b.1) = vertex t.colors a.2 b.2

private theorem valid_cons {s t pi d x y} (hd : ValidPairs s t pi d)
    (pass : pointOK s t pi d x y = true) : ValidPairs s t pi ((x,y)::d) := by
  intro a ha b hb
  have test := List.all_eq_true.mp pass
  rcases List.mem_cons.mp ha with rfl | ha
  · exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (test b hb)).1
  rcases List.mem_cons.mp hb with rfl | hb
  · exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (test a (List.mem_cons_of_mem _ ha))).2
  exact hd a ha b hb

private theorem move_entry {n : Nat} {ds pending : List Nat} {x : Nat} (hx : x ∈ pending)
    (h : (ds ++ pending).Perm (List.range n)) :
    ((x :: ds) ++ pending.erase x).Perm (List.range n) := by
  exact List.perm_middle.symm.trans
    (((List.perm_cons_erase hx).symm.append_left ds).trans h)

private theorem full_leaf {n : Nat} {s t pi} (fuel : Nat) (pending free : List Nat) (d : Assigned)
    (left : (d.map Prod.fst ++ pending).Perm (List.range n))
    (right : (d.map Prod.snd ++ free).Perm (List.range n))
    (valid : ValidPairs s t pi d) (hit : pointMap s t pi fuel pending free d = true) :
    ∃ w : Assigned, (w.map Prod.fst).Perm (List.range n) ∧
      (w.map Prod.snd).Perm (List.range n) ∧ ValidPairs s t pi w := by
  induction fuel generalizing pending free d with
  | zero =>
    have h := Bool.and_eq_true_iff.mp hit
    have hp : pending = [] := List.isEmpty_iff.mp h.1
    have hf : free = [] := List.isEmpty_iff.mp h.2
    exact ⟨d,by simpa [hp] using left,by simpa [hf] using right,valid⟩
  | succ n ih =>
    have ne : pending ≠ [] := by rintro rfl; simp [pointMap,nextChoice] at hit
    obtain ⟨x,hx,choose⟩ := pick (fun x => free.filter fun y => pointOK s t pi d x y) ne
    rw [pointMap,choose] at hit
    obtain ⟨y,hy,pass⟩ := List.any_eq_true.mp hit
    obtain ⟨hy,ok⟩ := List.mem_filter.mp hy
    exact ih _ _ ((x,y)::d) (move_entry hx left) (move_entry hy right) (valid_cons valid ok) pass

/-- A successful geometric search yields a genuine bijection on the points
that implements exactly the requested palette map on every ordered pair. -/
theorem pointSearch_sound {n : Nat} {s t : Scheme} {pi : List Nat}
    (pass : pointMap s t pi.toArray n (List.range n) (List.range n) [] = true) :
    ∃ e : Equiv.Perm (Fin n), ∀ i j,
      (pi[vertex s.colors i.val j.val]?).getD 0 = vertex t.colors (e i).val (e j).val := by
  obtain ⟨d,hl,hr,ok⟩ := full_leaf n (List.range n) (List.range n) [] (.refl _) (.refl _)
    (by simp [ValidPairs]) pass
  have chooseEntry (i : Fin n) : ∃ p ∈ d, p.1 = i.val := by
    exact List.mem_map.mp (hl.mem_iff.mpr (List.mem_range.mpr i.isLt))
  choose pair pair_mem source using chooseEntry
  have bounded (i : Fin n) : (pair i).2 < n :=
    List.mem_range.mp (hr.mem_iff.mp (List.mem_map_of_mem (pair_mem i)))
  let f := fun i => (⟨(pair i).2,bounded i⟩ : Fin n)
  have inj : Function.Injective f := by
    intro i j eq
    have same := List.inj_on_of_nodup_map (hr.nodup_iff.mpr List.nodup_range)
      (pair_mem i) (pair_mem j) (congrArg Fin.val eq)
    exact Fin.ext ((source i).symm.trans ((congrArg Prod.fst same).trans (source j)))
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj),fun i j => ?_⟩
  simpa only [source,pointColor,atN,List.getElem?_toArray] using ok (pair i) (pair_mem i) (pair j) (pair_mem j)

theorem pointTest_sound {s t : Scheme} {pi : List Nat} (pass : pointTest s t pi = true) :
    ∃ e : Equiv.Perm (Fin 16), ∀ i j,
      (pi[pointColor s i j]?).getD 0 = pointColor t (e i) (e j) :=
  pointSearch_sound pass

end QGI.SixteenMapSearch