import SixTenDesignGraph

namespace QGI.SixTen.Cross
open Finset
open private active leftOK nearLeft leftChecked share rightChecked size eligible coeff halfA halfB halfMask
  intersections diagonalValue diagonalOnly from SixTenDesignGraph

/-- No selection of the ten possible half-rows defines a directed relation
disjoint from its transpose. This checks the second alternative allowed for
basic relations, in addition to the symmetric check in SixTenDesignGraph. -/
private theorem noDirectedHalf : ∀ pick ∈ List.range 1024, ∃ i j : R,
    active (halfMask pick i) j=true ∧ active (halfMask pick j) i=true := by native_decide

theorem left_color_row (A : L → L → Bool) (diag : ∀ i, A i i=false)
    (law : ∀ (i : L) (j k : R), design i j=design i k →
      (univ.filter (fun x => A i x=true ∧ design x j=true)).card =
      (univ.filter (fun x => A i x=true ∧ design x k=true)).card)
    (i j k : L) (ne : j ≠ i) (nk : k ≠ i) : A i j=A i k := by
  let m := encode (A i)
  have bits (h : L) : active m h=A i h := decode _ _
  have ok : leftOK i m := ⟨(bits i).trans (diag i),fun j k eq => by
    simpa only [nearLeft,bits] using law i j k eq⟩
  rcases leftChecked i m (List.mem_range.mpr (encode_lt _)) ok with zero | full
  · simpa only [bits] using (zero j).trans (zero k).symm
  · rw [←bits j,←bits k,full,full]
    simp [ne,nk]

theorem directed_empty (A : R → R → Bool) (disjoint : ∀ i j, A i j=true → A j i=false)
    (regular : ∀ k j v, selectedDegree A k j=selectedDegree A k v)
    (mixed : ∀ k i h j, design i j=design h j → mixedDegree A k i j=mixedDegree A k h j)
    (i j : R) : A i j=false := by
  classical
  by_contra hn
  have nonzero : A i j=true := by cases h : A i j <;> simp_all
  have ij : i ≠ j := by rintro rfl; exact Bool.noConfusion (nonzero.symm.trans (disjoint i i nonzero))
  have shareSymm : ∀ i j : R, share i j=share j i := by native_decide
  obtain ⟨k,hk⟩ : ∃ k : Fin 2, share i j=k.val+1 := by
    rcases intersections i j ij with h|h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
  let cell := fun j w : R => A j w && decide (share j w=k.val+1)
  let m := fun j : R => encode (cell j)
  have bits (j w : R) : active (m j) w=cell j w := decode _ _
  have present : active (m i) j=true := by simp [bits,cell,hk,nonzero]
  have ok (j : R) : eligible (k.val+1) j (m j) := by
    constructor
    · intro w hw
      have test := (bits j w).symm.trans hw
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp test).2
    · intro i x eq
      simpa only [coeff,bits,cell,Bool.and_eq_true,decide_eq_true_eq,share,mixedDegree] using mixed (k.val+1) i x j eq
  have degrees (j : R) : size (m j)=selectedDegree A (k.val+1) 0 := by
    simpa only [size,bits,cell,Bool.and_eq_true,decide_eq_true_eq,share,selectedDegree] using regular (k.val+1) j 0
  have check (j : R) := rightChecked k j (m j) (List.mem_range.mpr (encode_lt _)) (ok j)
  simp only [degrees] at check
  by_cases empty : selectedDegree A (k.val+1) 0=0
  · simp only [empty,if_true] at check
    exact Bool.noConfusion (present.symm.trans (check i j))
  by_cases full : selectedDegree A (k.val+1) 0=(if k.val=0 then 6 else 3)
  · simp only [if_neg empty,if_pos full] at check
    have rev := check j i
    simp only [bits,cell,shareSymm j i,hk,decide_true,Bool.and_true,disjoint i j nonzero] at rev
    exact Bool.noConfusion rev
  simp only [empty,full,if_false] at check
  let pick := encode (fun j : R => decide (m j=halfB[j.val]!))
  have select (j : R) : halfMask pick j=m j := by
    change (if (encode _).testBit j.val then _ else _)=_
    rw [decode]
    by_cases hb : m j=halfB[j.val]!
    · simp [hb]
    · simpa only [hb,decide_false,Bool.false_eq_true,if_false] using ((check j).resolve_right hb).symm
  obtain ⟨u,v,h₁,h₂⟩ := noDirectedHalf pick (List.mem_range.mpr (encode_lt _))
  simp only [select,bits,cell,Bool.and_eq_true] at h₁ h₂
  exact Bool.noConfusion (h₂.1.symm.trans (disjoint u v h₁.1))

end QGI.SixTen.Cross
