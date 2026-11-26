import SixPointSearch
import SmallShoreLocal

namespace QGI.SixPointSearch
open Coherent.SmallShore
open scoped BigOperators

private theorem sorted_edge {e : Edge} (h : e.1 < e.2) : edge e.1 e.2 = e := by
  simp [edge, min_eq_left h.le, max_eq_right h.le]

private theorem edge_comm (i j : V) : edge j i = edge i j := by simp [edge, min_comm, max_comm]

private theorem regular_color {c : Table} {d : Nat} (hc : Local c d) (u v : V) :
    Regular (fun i j => decide (c i j = c u v)) := by
  have value (i : V) : degree (fun x y => decide (c x y = c u v)) i =
      steps c (c u v) (c v u) i i := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : c i j = c u v
    · simp [h, hc.reverse _ _ _ _ h]
    · simp [h]
  intro i
  rw [value, value]
  exact hc.products _ _ _ _ _ _ (((hc.diag i i).mpr rfl).trans ((hc.diag 0 0).mpr rfl).symm)

private theorem regular_either {c : Table} {s t : Nat}
    (hs : Regular (fun i j => decide (c i j = s)))
    (ht : Regular (fun i j => decide (c i j = t))) :
    Regular (fun i j => decide (c i j = s ∨ c i j = t)) := by
  by_cases eq : s = t
  · simpa [eq] using ht
  have value (i : V) : degree (fun x y => decide (c x y = s ∨ c x y = t)) i =
      degree (fun x y => decide (c x y = s)) i + degree (fun x y => decide (c x y = t)) i := by
    unfold degree
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases a : c i j = s <;> by_cases b : c i j = t <;> simp_all
  intro i
  rw [value, value, hs i, ht i]

/-- Remove the color of a selected edge together with its transpose. Both
colors have constant valency. The support is regular, and for a directed
pair the selected forward edges have constant outdegree as well. -/
private theorem next_atom {c : Table} {d : Nat} (hc : Local c d)
    (p : Edge) (tail : List Edge) (ordered : p.1 < p.2)
    (active : Nat → Prop) (region : ∀ i j, edge i j ∈ p::tail ↔ active (c i j)) :
    ∃ a ∈ atoms p tail, ∃ s t : Nat,
      (∀ i j, a.mark i j = if c i j = s then 1 else if c i j = t then 2 else 0) ∧
      (∀ i j, edge i j ∈ tail.filter (fun q => q ∉ a.support) ↔
        active (c i j) ∧ c i j ≠ s ∧ c i j ≠ t) := by
  classical
  let s := c p.1 p.2
  let t := c p.2 p.1
  have rev (i j : V) : c i j = s ↔ c j i = t :=
    ⟨fun h => hc.reverse _ _ _ _ h, fun h => hc.reverse _ _ _ _ h⟩
  have swap (i j : V) : (c j i=s ∨ c j i=t) ↔ (c i j=s ∨ c i j=t) := by
    rw [rev j i, ← rev i j, or_comm]
  have orbit (i j : V) :
      (c (edge i j).1 (edge i j).2 = s ∨ c (edge i j).1 (edge i j).2 = t) ↔
      (c i j = s ∨ c i j = t) := by
    rcases le_total i j with h | h
    · simp [edge, min_eq_left h, max_eq_right h]
    · simpa [edge, min_eq_right h, max_eq_left h] using swap i j
  let select := fun q : Edge => decide (c q.1 q.2 = s ∨ c q.1 q.2 = t)
  let S := (p::tail).filter select
  have chosen : select p = true := by simp [select,s]
  have src : active s := (region _ _).mp (by rw [sorted_edge ordered]; simp)
  have tgt : active t := (region _ _).mp (by rw [edge_comm,sorted_edge ordered]; simp)
  have memS (i j : V) : edge i j ∈ S ↔ c i j=s ∨ c i j=t := by
    simp only [S, List.mem_filter, select, decide_eq_true_eq, region, orbit]
    exact and_iff_right_of_imp (fun h => h.elim (fun eq => eq.symm ▸ src) (fun eq => eq.symm ▸ tgt))
  have Sreg : Regular (fun i j => decide (edge i j ∈ S)) := by
    simp only [memS]
    exact regular_either (regular_color hc p.1 p.2) (regular_color hc p.2 p.1)
  have Sp : p ∈ S := by simp [S,chosen]
  have listed : S ∈ supports p tail := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_map.mpr ⟨tail.filter select, List.mem_sublists.mpr List.filter_sublist, ?_⟩,
      decide_eq_true Sreg⟩
    simp [S,chosen]
  have remainder (i j : V) : edge i j ∈ tail.filter (fun q => q ∉ S) ↔
        active (c i j) ∧ c i j ≠ s ∧ c i j ≠ t := by
    have skip : (p::tail).filter (fun q => decide (q ∉ S)) = tail.filter (fun q => decide (q ∉ S)) := by simp [Sp]
    rw [← skip]
    simp [region, memS, not_or]
  by_cases same : s=t
  · refine ⟨⟨S,none⟩, List.mem_flatMap.mpr ⟨S,listed,List.mem_cons_self⟩,s,t,?_,remainder⟩
    intro i j
    by_cases eq : c i j = t <;> simp [Atom.mark, memS, same, eq]
  · let F := S.filter (fun q => decide (c q.1 q.2 = s))
    let a : Atom := ⟨S,some F⟩
    have Fp : p ∈ F := List.mem_filter.mpr ⟨Sp,by simp [s]⟩
    have named (i j : V) : a.mark i j = if c i j=s then 1 else if c i j=t then 2 else 0 := by
      by_cases inS : edge i j ∈ S
      · have which := (memS i j).mp inS
        have orientation : (i ≤ j ↔ edge i j ∈ F) ↔ c i j = s := by
          have inF : edge i j ∈ F ↔ c (edge i j).1 (edge i j).2 = s := by
            simp only [F, List.mem_filter, decide_eq_true_eq, inS, true_and]
          rw [inF]
          by_cases le : i ≤ j
          · simp [le,edge,min_eq_left le,max_eq_right le]
          · have jl := le_of_not_ge le
            simp only [le, false_iff, edge, min_eq_right jl, max_eq_left jl]
            exact (not_congr (rev j i)).trans
              ⟨fun nt => which.resolve_right nt, fun hs ht => same (hs.symm.trans ht)⟩
        simp only [a,Atom.mark,if_pos inS,orientation]
        rcases which with h|h <;> simp [h, Ne.symm same]
      · have missing := mt (memS i j).mpr inS
        simp [a,Atom.mark,inS,not_or.mp missing |>.1,not_or.mp missing |>.2]
    have positive : Regular (fun i j => decide (a.mark i j = 1)) := by
      have eq (i j : V) : (a.mark i j = 1) ↔ c i j = s := by
        rw [named]; split_ifs <;> simp_all
      simp only [eq]
      exact regular_color hc p.1 p.2
    refine ⟨a, List.mem_flatMap.mpr ⟨S,listed,List.mem_cons_of_mem _ ?_⟩,s,t,named,remainder⟩
    apply List.mem_filter.mpr
    exact ⟨List.mem_map.mpr ⟨F,List.mem_filter.mpr
      ⟨List.mem_sublists.mpr List.filter_sublist,decide_eq_true Fp⟩, rfl⟩,decide_eq_true positive⟩


private theorem mark_lt (a : Atom) (i j : V) : a.mark i j < 3 := by
  rcases a with ⟨support, _ | f⟩ <;> simp only [Atom.mark] <;> split_ifs <;> decide

private theorem cons_equal (a : Atom) (as : List Atom) (i j x y : V) :
    code (a::as) i j = code (a::as) x y ↔
      a.mark i j = a.mark x y ∧ code as i j = code as x y := by
  simp only [code]
  have := mark_lt a i j
  have := mark_lt a x y
  omega

/-- Each step chooses the actual color orbit of its pivot. The colors still
active are exactly the edges left in the recursion. The resulting digits
distinguish every active color from every other color. -/
private theorem covered {c : Table} {d : Nat} (hc : Local c d) (fuel : Nat)
    (rest : List Edge) (size : rest.length ≤ fuel)
    (ordered : ∀ q ∈ rest, q.1 < q.2) (active : Nat → Prop)
    (region : ∀ i j, edge i j ∈ rest ↔ active (c i j)) :
    ∃ as ∈ generate fuel rest,
      (∀ i j x y, c i j = c x y → code as i j = code as x y) ∧
      (∀ i j x y, active (c i j) → code as i j = code as x y → c i j = c x y) := by
  induction fuel generalizing rest active with
  | zero =>
    have empty : rest=[] := List.length_eq_zero_iff.mp (by omega)
    subst rest
    exact ⟨[],by simp [generate], fun _ _ _ _ _ => rfl, fun i j _ _ h => (List.not_mem_nil ((region i j).mpr h)).elim⟩
  | succ k ih =>
    cases rest with
    | nil =>
      exact ⟨[],by simp [generate], fun _ _ _ _ _ => rfl, fun i j _ _ h => (List.not_mem_nil ((region i j).mpr h)).elim⟩
    | cons p tail =>
      obtain ⟨a,member,s,t,named,remaining⟩ :=
        next_atom hc p tail (ordered _ List.mem_cons_self) active region
      let rest' := tail.filter fun q => decide (q ∉ a.support)
      have bound : rest'.length ≤ k := by
        have h := List.length_filter_le (fun q => decide (q ∉ a.support)) tail
        simp only [List.length_cons] at size
        exact h.trans (by omega)
      obtain ⟨as,found,preserves,distinguishes⟩ := ih rest' bound
        (fun q h => ordered _ (List.mem_cons_of_mem _ (List.mem_filter.mp h).1))
        (fun v => active v ∧ v ≠ s ∧ v ≠ t) remaining
      refine ⟨a::as,List.mem_flatMap.mpr ⟨a,member,List.mem_map.mpr ⟨as,found,rfl⟩⟩,?_,?_⟩
      · intro i j x y eq
        exact (cons_equal ..).mpr ⟨by simp only [named,eq],preserves _ _ _ _ eq⟩
      · intro i j x y live eq
        obtain ⟨current,later⟩ := (cons_equal ..).mp eq
        rw [named,named] at current
        by_cases hs : c i j=s
        · by_cases sx : c x y = s
          · exact hs.trans sx.symm
          · rw [if_pos hs, if_neg sx] at current
            split at current <;> omega
        by_cases ht : c i j=t
        · by_cases tx : c x y = t
          · exact ht.trans tx.symm
          · rw [if_neg hs, if_pos ht] at current
            by_cases sx : c x y = s
            · rw [if_pos sx] at current; omega
            · rw [if_neg sx, if_neg tx] at current; omega
        exact distinguishes _ _ _ _ ⟨live,hs,ht⟩ later

theorem generated_partition {c : Table} {d : Nat} (hc : Local c d) :
    ∃ as ∈ generate 15 edges, ∀ i j x y,
      code as i j = code as x y ↔ c i j = c x y := by
  have has (q : Edge) : q ∈ edges ↔ q.1 < q.2 := by
    rcases q with ⟨x,y⟩
    simp [edges]
  have region (i j : V) : edge i j ∈ edges ↔ c i j ≠ d := by
    rw [has]
    apply Iff.trans _ (not_congr (hc.diag i j)).symm
    change min i j < max i j ↔ i ≠ j
    rcases le_total i j with h | h
    · rw [min_eq_left h,max_eq_right h]; exact ⟨ne_of_lt,lt_of_le_of_ne h⟩
    · rw [min_eq_right h,max_eq_left h]; exact ⟨fun h => (ne_of_lt h).symm,fun ne => lt_of_le_of_ne h ne.symm⟩
  obtain ⟨as,found,preserves,distinguishes⟩ :=
    covered hc 15 edges (by decide) (fun q h => (has q).mp h) (· ≠ d) region
  refine ⟨as,found,fun i j x y => ⟨?_,preserves i j x y⟩⟩
  intro h
  by_cases a : c i j = d
  · by_cases b : c x y = d
    · exact a.trans b.symm
    · exact (distinguishes _ _ _ _ b h.symm).symm
  · exact distinguishes _ _ _ _ a h

attribute [local irreducible] witnesses witness generate

/-- An accepted witness supplies the point permutation. A witness of
unequal intersection numbers contradicts the input configuration. -/
theorem of_checked (cells : Fin 8 → Table)
    (ok : (generate 15 edges).all (checked cells) = true)
    {c : Table} {d : Nat} (hc : Local c d) :
    ∃ k : Fin 8, ∃ e : Equiv.Perm V, ∀ i j x y,
      c (e i) (e j) = c (e x) (e y) ↔ cells k i j = cells k x y := by
  obtain ⟨as,found,agrees⟩ := generated_partition hc
  have pass := List.all_eq_true.mp ok as found
  let w := witness as
  by_cases pos : witness as % 2 = 0
  · simp only [checked, if_pos pos, decide_eq_true_eq] at pass
    obtain ⟨injective,matchColors⟩ := pass
    let f := fun i : V => digit (w/2/8) i.val
    let e := Equiv.ofBijective f ⟨injective, Finite.surjective_of_injective injective⟩
    exact ⟨_, e, fun i j x y => (agrees (e i) (e j) (e x) (e y)).symm.trans (matchColors i j x y)⟩
  · simp only [checked, if_neg pos, decide_eq_true_eq] at pass
    obtain ⟨same,unequal⟩ := pass
    have step (a b i j : V) : steps (code as) (code as 0 a) (code as 0 b) i j =
        steps c (c 0 a) (c 0 b) i j := by simp only [steps,agrees]
    rw [step,step] at unequal
    exact (unequal (hc.products _ _ _ _ _ _ ((agrees _ _ _ _).mp same))).elim
 
end QGI.SixPointSearch
