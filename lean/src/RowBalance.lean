import RowValencies
import RowSupports

namespace QGI.RowCensus

variable {n : Nat} [NeZero n] {α : Type} [DecidableEq α] {m : Table n α}

def fiber (m : Table n α) (i : Fin n) (a : α) := Finset.univ.filter fun j => m i j=a
def degree (m : Table n α) (a : α) := (fiber m 0 a).card
def pairNum (m : Table n α) (i j : Fin n) (a b : α) :=
  (Finset.univ.filter fun z => m i z=a ∧ m j z=b).card

theorem fiber_card (h : Laws m) (i : Fin n) (a : α) : (fiber m i a).card=degree m a := by
  simpa only [degree,fiber,← countFiber] using (h.row_perm i).count_eq a

private theorem pairs_eq (h : Laws m) (i j x y : Fin n) (e : m i j=m x y) (a b : α) :
    pairNum m i j a b=pairNum m x y a b := by
  have hp := (h.pairs _ _ _ _ e).count_eq (a,b)
  simpa only [countFiber,Prod.mk.injEq,pairNum] using hp

theorem degree_reverse (h : Laws m) (i j : Fin n) : degree m (m i j)=degree m (m j i) := by
  let R := fun x y => m x y=m i j
  have a (x : Fin n) (_ : x∈Finset.univ) :
      (Finset.univ.bipartiteAbove R x).card=degree m (m i j) := fiber_card h x _
  have b (y : Fin n) (_ : y∈Finset.univ) :
      (Finset.univ.bipartiteBelow R y).card=degree m (m j i) := by
    convert fiber_card h y (m j i) using 2
    ext z
    simp only [Finset.bipartiteBelow,fiber,Finset.mem_filter,Finset.mem_univ,true_and,R]
    exact ⟨h.reverse _ _ _ _,h.reverse _ _ _ _⟩
  have eq := Finset.card_mul_eq_card_mul R a b
  simpa [NeZero.ne n] using eq

/-- Count triangles in the two orders around a fixed vertex. -/
theorem triangle_dvd (h : Laws m) (i j : Fin n) (a b : α) :
    degree m a ∣ degree m (m i j)*pairNum m i j a b := by
  by_cases hit : ∃ s, m i s=a ∧ m j s=b
  · obtain ⟨z,rfl,rfl⟩ := hit
    let R := fun x y => m x y=m j z
    let S := fiber m i (m i j)
    let T := fiber m i (m i z)
    have top (x : Fin n) (hx : x∈S) :
        (T.bipartiteAbove R x).card=pairNum m i j (m i z) (m j z) := by
      have same := (Finset.mem_filter.mp hx).2
      calc
        _ = pairNum m i x (m i z) (m j z) := by
          unfold T Finset.bipartiteAbove fiber pairNum R
          rw [Finset.filter_filter]
        _ = _ := pairs_eq h _ _ _ _ same _ _
    have bot (y : Fin n) (hy : y∈T) :
        (S.bipartiteBelow R y).card=pairNum m i z (m i j) (m z j) := by
      have same := (Finset.mem_filter.mp hy).2
      calc
        _ = pairNum m i y (m i j) (m z j) := by
          unfold S Finset.bipartiteBelow fiber pairNum R
          rw [Finset.filter_filter]
          congr 1
          ext t
          simp only [Finset.mem_filter,Finset.mem_univ,true_and]
          exact and_congr_right fun _ => ⟨h.reverse _ _ _ _,h.reverse _ _ _ _⟩
        _ = _ := pairs_eq h _ _ _ _ same _ _
    exact ⟨_,by simpa only [S,T,fiber_card h] using Finset.card_mul_eq_card_mul R top bot⟩
  · have zero : pairNum m i j a b=0 := Finset.card_eq_zero.mpr
      (Finset.filter_eq_empty_iff.mpr fun s _ mem => hit ⟨s,mem⟩)
    simp [zero]

def balancedNext (n : Nat) (rs : List Nat) (w : Nat) : Bool :=
  let first := List.ofFn fun j : Fin n => entry n rs 0 j.val
  (List.range rs.length).all fun i =>
    let r := rs.getD i 0
    let v := first.count (digit n r rs.length)
    let pairs := List.ofFn fun j : Fin n => (digit n r j.val,digit n w j.val)
    v==first.count (digit n w i) && pairs.all fun p =>
      let value := v*pairs.count p
      decide (first.count p.1 ∣ value ∧ first.count p.2 ∣ value)

def balancedRows (n : Nat) (rs : List Nat) :=
  (supportedRows n rs).filter (balancedNext n rs)

theorem balanced_complete (m : Matrix n) (h : Laws m) (rs : List Nat)
    (f : Fits m rs) (pos : 0<rs.length) (k : Fin n) (hk : k.val=rs.length) :
    word m k ∈ balancedRows n rs := by
  apply List.mem_filter.mpr
  refine ⟨supported_complete m h rs f pos k hk,?_⟩
  have vals (j : Fin n) : entry n rs 0 j.val=(m 0 j).val := f 0 j pos
  have number (a : Fin n) : (List.ofFn fun j : Fin n => entry n rs 0 j.val).count a.val=degree m a := by
    simp only [vals,countFiber,degree,fiber,Fin.val_inj]
  apply List.all_eq_true.mpr
  intro i hi
  have ilt := List.mem_range.mp hi
  let x : Fin n := ⟨i,lt_of_lt_of_le ilt (by simpa [← hk] using k.isLt.le)⟩
  have rw1 (z : Fin n) : digit n (rs.getD i 0) z.val=(m x z).val := f x z ilt
  have edge : digit n (rs.getD i 0) rs.length=(m x k).val := hk ▸ rw1 k
  have rev : digit n (word m k) i=(m k x).val := digit_word m k x
  apply Bool.and_eq_true_iff.mpr
  constructor
  · exact beq_iff_eq.mpr (by rw [edge,rev,number,number,degree_reverse h])
  · apply List.all_eq_true.mpr
    intro p hp
    obtain ⟨z,rfl⟩ := List.mem_ofFn.mp hp
    simp only [rw1,digit_word,edge,number,decide_eq_true_eq,countFiber,Prod.mk.injEq,Fin.val_inj]
    have cnt : (List.ofFn (fun j : Fin n => ((m x j).val,(m k j).val))).count
        ((m x z).val,(m k z).val) = pairNum m x k (m x z) (m k z) := by
      change List.countP _ _=_
      rw [List.countP_eq_length_filter,length_filter_ofFn]
      simp [pairNum,Fin.val_inj]
    rw [cnt]
    refine ⟨triangle_dvd h x k _ _,?_⟩
    have q := triangle_dvd h k x (m k z) (m x z)
    rw [degree_reverse h k x] at q
    convert q using 2
    unfold pairNum
    simp only [and_comm]

end QGI.RowCensus
