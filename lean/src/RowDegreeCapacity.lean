import RowPredictions

namespace QGI.RowCensus

private def forced (r : List Nat) (a k : Nat) :=
  r.dedup.all fun b => b==a || (List.range (r.count b + 1)).all fun p =>
    p==0 || !(decide (r.count a ∣ r.count k*p))

def capacity (r : List Nat) := r.dedup.all fun a => (r.filter (forced r a)).length ≤ r.count a

/-- Fix an a-neighbor z of the basepoint. For each y, the triangle count
for its color toward z is positive and bounded by that color's valency.
Divisibility can force that color to be a, so there are at most d(a)
such vertices y. -/
theorem capacity_sound {n : Nat} [NeZero n] (m : Matrix n) (h : Laws m) :
    capacity (wordDigits n (word m 0))=true := by
  let r := wordDigits n (word m 0)
  have cnt (a : Fin n) : r.count a.val=degree m a := by
    simp only [r,wordDigits,digit_word,countFiber,Fin.val_inj,degree,fiber]
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨z,eq⟩ := List.mem_ofFn.mp (List.mem_dedup.mp ha)
  simp only [digit_word] at eq
  subst a
  let a := m 0 z
  have forces (y : Fin n) (test : forced r a.val (m 0 y).val=true) : m y z=a := by
    let b := m y z
    let p := pairNum m 0 y a b
    have pos : 0<p := Finset.card_pos.mpr ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl,rfl⟩⟩
    have upper : p≤degree m b := (Finset.card_le_card (show
        Finset.univ.filter (fun w => m 0 w=a ∧ m y w=b) ⊆ fiber m y b from
        fun w hw => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2.2⟩)).trans_eq (fiber_card h _ _)
    have occurs := (h.row_perm y).mem_iff.mp (List.mem_ofFn.mpr ⟨z,rfl⟩)
    obtain ⟨w,hw⟩ := List.mem_ofFn.mp occurs
    have inside : b.val∈r.dedup := List.mem_dedup.mpr (List.mem_ofFn.mpr ⟨w,by simp [b,hw]⟩)
    rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp test _ inside) with hit|other
    · exact Fin.ext (beq_iff_eq.mp hit)
    · have lim : p<r.count b.val+1 := (cnt b) ▸ Nat.lt_succ_of_le upper
      have fail := List.all_eq_true.mp other p (List.mem_range.mpr lim)
      have div := triangle_dvd h 0 y a b
      simp only [beq_iff_eq,Bool.or_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,cnt] at fail
      exact (fail.elim (fun zero => (Nat.ne_of_gt pos) zero) (fun no => no div)).elim
  let allowed := Finset.univ.filter fun y : Fin n => forced r a.val (m 0 y).val
  have incl : allowed ⊆ fiber m z (m z 0) := fun y hy =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.reverse _ _ _ _ (forces y (Finset.mem_filter.mp hy).2)⟩
  have bound := (Finset.card_le_card incl).trans_eq ((fiber_card h z _).trans (degree_reverse h z 0))
  have count : (r.filter (forced r a.val)).length=allowed.card := by
    rw [show r=List.ofFn (fun y => (m 0 y).val) by simp [r,wordDigits],length_filter_ofFn]
    simpa only [allowed,r,wordDigits,digit_word,Nat.cast_id] using
      Finset.sum_boole (α:=Nat) (fun y : Fin n => forced r a.val (m 0 y).val=true) Finset.univ
  exact decide_eq_true (count ▸ (by simpa only [cnt] using bound : allowed.card≤r.count a.val))

end QGI.RowCensus
