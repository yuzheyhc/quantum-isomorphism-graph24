import BinaryVectorChoice

namespace QGI.TernaryVectorChoice
open scoped InnerProductSpace
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A three-by-three vector table with orthogonal rows and columns and a
common nonzero sum admits a permutation with pairwise nonorthogonal entries. -/
theorem local_choice (ξ : E) (nz : ξ≠0) (u : Fin 3 → Fin 3 → E)
    (rows : ∀ i, ∑ a, u i a=ξ) (cols : ∀ a, ∑ i, u i a=ξ)
    (ro : ∀ i a b, a≠b → ⟪u i a,u i b⟫_𝕜=0) (co : ∀ a i j, i≠j → ⟪u i a,u j a⟫_𝕜=0) :
    ∃ e : Equiv.Perm (Fin 3), ∀ i j, ⟪u i (e i),u j (e j)⟫_𝕜≠0 := by
  classical
  obtain ⟨a,ha⟩ : ∃ a, u 0 a≠0 := by
    by_contra! h
    exact nz ((rows 0).symm.trans (by simp [h]))
  have self : ⟪u 0 a,ξ⟫_𝕜≠0 := by
    rw [←rows 0,inner_sum,Finset.sum_eq_single a]
    · exact fun h => ha (inner_self_eq_zero.mp h)
    · exact fun b _ h => ro 0 a b h.symm
    · simp
  obtain ⟨b,hb⟩ : ∃ b, ⟪u 0 a,u 1 b⟫_𝕜≠0 := by
    by_contra! h
    apply self
    rw [←rows 1,inner_sum]
    simp [h]
  have ne : a≠b := by rintro rfl; exact hb (co a 0 1 (by decide))
  obtain ⟨e,ea,eb⟩ := (show ∀ a b : Fin 3, a≠b → ∃ e : Equiv.Perm (Fin 3), e 0=a ∧ e 1=b by decide) a b ne
  let v := fun i j => u i (e j)
  have r (i) : v i 0+v i 1+v i 2=ξ := by
    rw [←Fin.sum_univ_three,←rows i]; exact Equiv.sum_comp e (u i)
  have c (j) : v 0 j+v 1 j+v 2 j=ξ := by
    simpa only [Fin.sum_univ_three,v] using cols (e j)
  have rv (i j k : Fin 3) (h : j≠k) : ⟪v i j,v i k⟫_𝕜=0 := ro _ _ _ (e.injective.ne h)
  have cv (j i k : Fin 3) (h : i≠k) : ⟪v i j,v k j⟫_𝕜=0 := co _ _ _ h
  have n01 : ⟪v 0 0,v 1 1⟫_𝕜≠0 := by simpa only [v,ea,eb] using hb
  have n10 : ⟪v 1 1,v 0 0⟫_𝕜≠0 := mt inner_eq_zero_symm.mp n01
  have n02 : ⟪v 0 0,v 2 2⟫_𝕜≠0 := by
    have h := congrArg (fun z => ⟪v 0 0,z⟫_𝕜) ((r 1).trans (c 2).symm)
    simp only [inner_add_right,cv 0 0 1 (by decide),rv 0 0 2 (by decide),zero_add] at h
    exact fun z => n01 (by rw [z,add_zero] at h; exact add_right_cancel (h.trans (zero_add _).symm))
  have n12 : ⟪v 1 1,v 2 2⟫_𝕜≠0 := by
    have h := congrArg (fun z => ⟪v 1 1,z⟫_𝕜) ((r 0).trans (c 2).symm)
    simp only [inner_add_right,cv 1 1 0 (by decide),rv 1 1 2 (by decide),add_zero] at h
    exact fun z => n10 (by rw [z,add_zero] at h; exact add_right_cancel (h.trans (zero_add _).symm))
  have n00 : ⟪v 0 0,v 0 0⟫_𝕜≠0 := fun h => n01 (by rw [inner_self_eq_zero.mp h,inner_zero_left])
  have n11 : ⟪v 1 1,v 1 1⟫_𝕜≠0 := fun h => n01 (by rw [inner_self_eq_zero.mp h,inner_zero_right])
  have n22 : ⟪v 2 2,v 2 2⟫_𝕜≠0 := fun h => n02 (by rw [inner_self_eq_zero.mp h,inner_zero_right])
  refine ⟨e,fun i j => ?_⟩
  change ⟪v i i,v j j⟫_𝕜≠0
  fin_cases i <;> fin_cases j <;> first | assumption | exact mt inner_eq_zero_symm.mp n02 | exact mt inner_eq_zero_symm.mp n12

/-- If all tables agree after row and column relabeling, the choice in one
table gives nonorthogonal entries simultaneously across every table. -/
theorem synchronize {I : Type*} (o : I) (ξ : E) (nz : ξ≠0) (u : I → Fin 3 → Fin 3 → E)
    (rows : ∀ i, ∑ a, u o i a=ξ) (cols : ∀ a, ∑ i, u o i a=ξ)
    (ro : ∀ i a b, a≠b → ⟪u o i a,u o i b⟫_𝕜=0) (co : ∀ a i j, i≠j → ⟪u o i a,u o j a⟫_𝕜=0)
    (transport : ∀ s, ∃ f g : Equiv.Perm (Fin 3), ∀ i a, u o i a=u s (f i) (g a)) :
    ∃ e : I → Equiv.Perm (Fin 3), ∀ s t i j, ⟪u s i (e s i),u t j (e t j)⟫_𝕜≠0 := by
  obtain ⟨p,hp⟩ := local_choice ξ nz (u o) rows cols ro co
  choose f g equal using transport
  let e := fun s => (f s).symm.trans (p.trans (g s))
  refine ⟨e,fun s t i j => ?_⟩
  obtain ⟨i,rfl⟩ := (f s).surjective i
  obtain ⟨j,rfl⟩ := (f t).surjective j
  simpa only [e,Equiv.trans_apply,Equiv.symm_apply_apply,←equal] using hp i j

/-- In two decompositions of the same vector, an entry which can overlap
only its designated partner in either direction equals that partner. -/
theorem match_entry (ξ : E) (u v : Fin 3 → E) (su : ∑ a, u a=ξ) (sv : ∑ a, v a=ξ)
    (a b : Fin 3) (uo : ∀ t, t≠a → ⟪u a,u t⟫_𝕜=0) (vo : ∀ t, t≠b → ⟪v b,v t⟫_𝕜=0)
    (uv : ∀ t, t≠b → ⟪u a,v t⟫_𝕜=0) (vu : ∀ t, t≠a → ⟪v b,u t⟫_𝕜=0) : u a=v b := by
  have left (x : E) (f : Fin 3 → E) (s : ∑ t, f t=ξ) (i : Fin 3)
      (others : ∀ t, t≠i → ⟪x,f t⟫_𝕜=0) : ⟪x,ξ⟫_𝕜=⟪x,f i⟫_𝕜 := by
    rw [←s,inner_sum]; exact Finset.sum_eq_single i (fun t _ ne => others t ne) (by simp)
  have uu := (left (u a) u su a uo).symm.trans (left (u a) v sv b uv)
  have vv := (left (v b) v sv b vo).symm.trans (left (v b) u su a vu)
  have zero : ⟪u a-v b,u a-v b⟫_𝕜=0 := by
    simp only [inner_sub_left,inner_sub_right,uu,vv,sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp zero)

end QGI.TernaryVectorChoice

