import Synchrony

namespace QGI.BinaryVectorChoice

open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Equal norms use a single order on the vector space, shared by all pairs. -/
private noncomputable def pick [LinearOrder E] (x y : E) : E := by
  classical
  exact if ‖x‖ = ‖y‖ then max x y else if ‖x‖ < ‖y‖ then y else x

private theorem pick_comm [LinearOrder E] (x y : E) : pick x y = pick y x := by
  rcases lt_trichotomy ‖x‖ ‖y‖ with h | h | h
  · simp [pick, h, h.ne, h.ne', not_lt_of_gt h]
  · simp [pick, h, max_comm]
  · simp [pick, h, h.ne, h.ne', not_lt_of_gt h]

private theorem pick_spec [LinearOrder E] (x y : E) :
    (pick x y = x ∧ ‖y‖ ≤ ‖x‖) ∨ (pick x y = y ∧ ‖x‖ ≤ ‖y‖) := by
  rcases lt_trichotomy ‖x‖ ‖y‖ with h | h | h
  · exact Or.inr ⟨by simp [pick, h, h.ne], h.le⟩
  · rcases le_total x y with hxy | hyx
    · exact Or.inr ⟨by simp [pick, h, max_eq_right hxy], h.le⟩
    · exact Or.inl ⟨by simp [pick, h, max_eq_left hyx], h.ge⟩
  · exact Or.inl ⟨by simp [pick, h.ne', not_lt_of_gt h], h.le⟩

/-- Two orthogonal summands with at least half the squared norm each exhaust ξ. -/
private theorem exhaustive {ξ x y : E} (xperp : ⟪x, ξ - x⟫_𝕜 = 0)
    (yperp : ⟪y, ξ - y⟫_𝕜 = 0) (xy : ⟪x, y⟫_𝕜 = 0)
    (hx : ‖ξ‖ ^ 2 ≤ 2 * ‖x‖ ^ 2) (hy : ‖ξ‖ ^ 2 ≤ 2 * ‖y‖ ^ 2) :
    x + y = ξ := by
  let r := ξ - (x + y)
  rw [inner_sub_right, sub_eq_zero] at xperp yperp
  have xr : ⟪x, r⟫_𝕜 = 0 := by simp [r, inner_sub_right, inner_add_right, xperp, xy]
  have yr : ⟪y, r⟫_𝕜 = 0 := by
    simp [r, inner_sub_right, inner_add_right, yperp, inner_eq_zero_symm.mp xy]
  have sr : ⟪x + y, r⟫_𝕜 = 0 := by rw [inner_add_left, xr, yr, add_zero]
  have sum : x + y + r = ξ := by dsimp [r]; abel
  have norms := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x + y) r sr
  rw [sum, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y xy] at norms
  have rz : ‖r‖ = 0 := by nlinarith [sq_nonneg ‖r‖]
  have rzero : r = 0 := norm_eq_zero.mp rz
  rwa [rzero, add_zero] at sum

/-- Given orthogonal decompositions of one nonzero vector, pick a nonzero
summand from each so that all chosen inner products are nonzero. -/
theorem exists_selection (ξ : E) (hξ : ξ ≠ 0) (u v : ι → E)
    (sum : ∀ i, u i + v i = ξ) (orth : ∀ i, ⟪u i, v i⟫_𝕜 = 0) :
    ∃ x : ι → E, (∀ i, x i = u i ∨ x i = v i) ∧ (∀ i, x i ≠ 0) ∧
      ∀ i j, ⟪x i, x j⟫_𝕜 ≠ 0 := by
  classical
  letI : LinearOrder E := linearOrderOfSTO WellOrderingRel
  let x := fun i => pick (u i) (v i)
  let y := fun i => ξ - x i
  have data (i : ι) : ((x i = u i ∧ y i = v i) ∨ (x i = v i ∧ y i = u i)) ∧
      ‖y i‖ ≤ ‖x i‖ := by
    rcases pick_spec (u i) (v i) with ⟨h, hn⟩ | ⟨h, hn⟩
    · have hy : y i = v i := by simp [y, x, h, ← sum i]
      exact ⟨Or.inl ⟨h, hy⟩, by simpa only [x, h, hy] using hn⟩
    · have hy : y i = u i := by simp [y, x, h, ← sum i]
      exact ⟨Or.inr ⟨h, hy⟩, by simpa only [x, h, hy] using hn⟩
  have perp (i : ι) : ⟪x i, y i⟫_𝕜 = 0 := by
    rcases (data i).1 with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hx, hy, orth i]
    · rw [hx, hy]; exact inner_eq_zero_symm.mp (orth i)
  have fixed (i : ι) : pick (x i) (y i) = x i := by
    rcases (data i).1 with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hx, hy]; exact hx
    · rw [hx, hy, pick_comm]; exact hx
  have dom (i : ι) : ‖ξ‖ ^ 2 ≤ 2 * ‖x i‖ ^ 2 := by
    have s : x i + y i = ξ := by dsimp [y]; abel
    have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x i) (y i) (perp i)
    rw [s] at hp
    nlinarith only [hp, mul_self_le_mul_self (norm_nonneg _) (data i).2]
  have nz (i : ι) : x i ≠ 0 := by
    intro h
    have bound := dom i
    rw [h, norm_zero] at bound
    have : ‖ξ‖ = 0 := by nlinarith
    exact hξ (norm_eq_zero.mp this)
  refine ⟨x, fun i => (data i).1.imp And.left And.left, nz, ?_⟩
  intro i j opposite
  have full := exhaustive (perp i) (perp j) opposite (dom i) (dom j)
  have yi : y i = x j := by simp [y, ← full]
  have yj : y j = x i := by simp [y, ← full]
  have same : x i = x j := by
    calc
      x i = pick (x i) (x j) := by simpa only [yi] using (fixed i).symm
      _ = pick (x j) (x i) := pick_comm _ _
      _ = x j := by simpa only [yj] using fixed j
  rw [← same] at opposite
  exact nz i (inner_self_eq_zero.mp opposite)

/-- If each row has two candidate images, orthogonality for repeated images
and for mismatched ordered-pair colors yields one color-preserving bijection.
A row with only one possible image can use zero as its second vector. -/
theorem color_equiv_of_binary_candidates {n : Nat} {C : Type*}
    (ξ : E) (hξ : ξ ≠ 0) (candidate : Fin n → Bool → Fin n) (v : Fin n → Bool → E)
    (sum : ∀ i, v i false + v i true = ξ) (orth : ∀ i, ⟪v i false, v i true⟫_𝕜 = 0)
    (G H : Fin n → Fin n → C)
    (sameImage : ∀ i j a b, i ≠ j → candidate i a = candidate j b → ⟪v i a, v j b⟫_𝕜 = 0)
    (mismatch : ∀ i j a b, G i j ≠ H (candidate i a) (candidate j b) →
      ⟪v i a, v j b⟫_𝕜 = 0) :
    ∃ f : Fin n ≃ Fin n, (∀ i, ∃ b, f i = candidate i b ∧ v i b ≠ 0) ∧
      ∀ i j, G i j = H (f i) (f j) := by
  classical
  obtain ⟨x, member, nonzero, together⟩ := exists_selection ξ hξ _ _ sum orth
  have label (i : Fin n) : ∃ b, x i = v i b := by
    rcases member i with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  let b := fun i => (label i).choose
  have hb (i : Fin n) : x i = v i (b i) := (label i).choose_spec
  let f := fun i => candidate i (b i)
  have ok (i j : Fin n) : ⟪v i (b i), v j (b j)⟫_𝕜 ≠ 0 := by
    simpa only [← hb] using together i j
  have inj : Function.Injective f := by
    intro i j equal
    by_contra distinct
    exact ok i j (sameImage i j (b i) (b j) distinct equal)
  refine ⟨Equiv.ofBijective f ⟨inj, Finite.injective_iff_surjective.mp inj⟩, ?_, ?_⟩
  · intro i
    exact ⟨b i, rfl, hb i ▸ nonzero i⟩
  · intro i j
    by_contra bad
    exact ok i j (mismatch i j (b i) (b j) bad)

/-- Two allowed images on any common nonzero vector in the strategy's
cyclic space suffice. The allowed labels can coincide. -/
theorem isomorphic_on_cyclic {n : Nat} {G H : Graph n} {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)
    (ξ : Synchrony.cyclic p) (nonzero : ξ ≠ 0)
    (support : ∀ i : Fin n, ∃ a b : Fin n, ∀ k : Fin n,
      Synchrony.restricted p (false,i) k ξ ≠ 0 → k = a ∨ k = b) : Isomorphic G H := by
  classical
  choose a b allowed using support
  let row := fun (i k : Fin n) => Synchrony.restricted p (false,i) k ξ
  let label := fun (i : Fin n) (s : Bool) => if s then b i else a i
  let vec := fun (i : Fin n) (s : Bool) =>
    if s && decide (a i = b i) then 0 else row i (label i s)
  have sum (i : Fin n) : vec i false + vec i true = ξ := by
    have truncated : ∑ j ∈ ({a i, b i} : Finset (Fin n)), row i j = ξ := by
      calc
        _ = ∑ j : Fin n, row i j := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ outside
          by_contra nz
          exact outside (by simpa only [Finset.mem_insert, Finset.mem_singleton] using allowed i j nz)
        _ = ξ := by
          apply Subtype.ext
          change (Synchrony.cyclic p).subtype (∑ j, row i j) = _
          rw [map_sum]
          exact (Synchrony.magic_sums p i ξ).1
    by_cases h : a i = b i <;> simpa [vec, label, h] using truncated
  have bad (i j : Fin n) (s t : Bool)
      (loss : Loses G H (false,i) (false,j) (label i s) (label j t)) :
      ⟪vec i s, vec j t⟫_ℂ = 0 := by
    have h : ⟪row i (label i s), row j (label j t)⟫_ℂ = 0 := by
      let A := Synchrony.restricted p (false,i) (label i s)
      let B := Synchrony.restricted p (false,j) (label j t)
      have zero : A (B ξ) = 0 := congrArg (fun F : Module.End ℂ (Synchrony.cyclic p) => F ξ)
        (Synchrony.restricted_mismatch p _ _ _ _ loss)
      change ⟪(A ξ : K),(B ξ : K)⟫_ℂ = 0
      rw [(Synchrony.restricted_projection p _ _).2,zero]
      simp
    dsimp only [vec]
    split_ifs <;> simp [h]
  have orth (i : Fin n) : ⟪vec i false, vec i true⟫_ℂ = 0 := by
    by_cases h : a i = b i
    · simp [vec, h]
    · apply bad
      intro equality
      have clash := congrArg (fun z : Bool × Bool => z.1) equality
      simp [rel, ends, label, h] at clash
  obtain ⟨f, _, edges⟩ := color_equiv_of_binary_candidates ξ nonzero
    label vec sum orth G.edge H.edge (by
      intro i j s t distinct same
      apply bad
      intro equality
      have clash := congrArg (fun z : Bool × Bool => z.1) equality
      simp [rel, ends, distinct, same] at clash) (by
      intro i j s t different
      apply bad
      exact fun equal => different (congrArg (fun z : Bool × Bool => z.2) equal))
  exact ⟨⟨f, f.symm, f.symm_apply_apply, f.apply_symm_apply, edges⟩⟩

/-- Specialization to the original unit strategy vector. -/
theorem isomorphic_of_two_images {n : Nat} {G H : Graph n} {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)
    (support : ∀ i : Fin n, ∃ a b : Fin n, ∀ k : Fin n,
      p.alice (false, i) k p.psi ≠ 0 → k = a ∨ k = b) : Isomorphic G H := by
  let ξ : Synchrony.cyclic p := ⟨p.psi,Synchrony.psi_mem p⟩
  apply isomorphic_on_cyclic p ξ (fun h => Synchrony.psi_ne_zero p (congrArg Subtype.val h))
  intro i
  obtain ⟨a,b,hs⟩ := support i
  exact ⟨a,b,fun k h => hs k (fun z => h (Subtype.ext z))⟩

end QGI.BinaryVectorChoice
