import CoprimeBlocks

noncomputable section
namespace QGI.Coherent.SmallFiberElimination
open Relations FiberRectangles
variable {n : Nat} (G : Graph n)
abbrev c := color (closure G)

private theorem member (i j : Fin n) : i ∈ fiber G j ↔ c G i i = c G j j :=
  mem_fiber.trans (same _ _ _ _ _).symm

private theorem coordinates (x : Fin n) : ∃ f : Fin (fiber G x).card ↪ Fin n,
    ∀ i, (∃ j, f j=i) ↔ i ∈ fiber G x := by
  let s := fiber G x
  let u : Fin s.card ≃ {k // k ∈ s} := (Fintype.equivFinOfCardEq (Fintype.card_coe s)).symm
  let f : Fin s.card ↪ Fin n := u.toEmbedding.trans (Function.Embedding.subtype _)
  exact ⟨f,fun i => ⟨by rintro ⟨j,rfl⟩; exact (u j).property,
    fun h => ⟨u.symm ⟨i,h⟩,congrArg Subtype.val (u.apply_symm_apply _)⟩⟩⟩

theorem single_row (a b : Fin n) (small : (fiber G b).card ≤ 3)
    (mixed : ∃ i ∈ fiber G a, ∃ j ∈ fiber G b, c G i j ≠ c G a b) :
    ∃ i ∈ fiber G a, ∃ j ∈ fiber G b, ∀ z, c G i z = c G i j → z=j := by
  obtain ⟨f,hf⟩ := coordinates G a
  obtain ⟨g,hg⟩ := coordinates G b
  obtain ⟨i,hi,j,hj,ne⟩ := mixed
  obtain ⟨x,rfl⟩ := (hf _).mpr hi
  obtain ⟨y,rfl⟩ := (hg _).mpr hj
  obtain ⟨s,hs⟩ := (hf _).mpr ((member G _ _).mpr rfl)
  obtain ⟨t,ht⟩ := (hg _).mpr ((member G _ _).mpr rfl)
  have different : c G (f x) (g y) ≠ c G (f s) (g t) := by rwa [hs,ht]
  obtain ⟨v,q,_,hit⟩ := surjection_of_small_fiber
    (CoprimeFibers.biregular G f.injective g.injective hf hg) small ⟨x,y,s,t,different⟩
  refine ⟨f x,(hf _).mp ⟨x,rfl⟩,g (q x),(hg _).mp ⟨_,rfl⟩,fun z eq => ?_⟩
  have diag := (end_colors (closure G) eq).2
  obtain ⟨u,rfl⟩ := (hg _).mpr ((member G _ _).mpr (diag.trans ((member G _ _).mp ((hg _).mp ⟨q x,rfl⟩))))
  exact congrArg g ((hit x u).mp (eq.trans ((hit x (q x)).mpr rfl))).symm

variable {G}
/-- A fiber of at most three may be deleted when at most thirteen points
remain. A nonuniform cross color determines its points by a function.
If every cross rectangle is uniform, the separate point maps glue. -/
theorem realize {H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (b : Fin n) (size : (fiber G b).card ≤ 3)
    (pos : 0 < n - (fiber G b).card) (rest : n - (fiber G b).card ≤ 13) :
    ∃ e : Equiv.Perm (Fin n), ∀ i j, c G i j = StrategyColorLaws.targetName p (e i) (e j) := by
  classical
  let F := fiber G b
  have sameFiber {u : Fin n} (hu : u ∈ F) : fiber G u = F := by
    ext z
    simp only [F,member,(member G _ _).mp hu]
  by_cases uniform : ∀ x, x ∉ F → ∀ i ∈ fiber G x, ∀ j ∈ F, c G i j = c G x b
  · let block := fun v : Nat => if v = c G b b then 0 else 1
    have atPoint (i : Fin n) : block (c G i i) = if i ∈ F then 0 else 1 := by simp [F,block,member]
    apply CoprimeBlocks.realize_uniform p block
    · intro k
      change (Finset.univ.filter (fun i => block (c G i i) = k)).card ≤ 13
      simp_rw [atPoint]
      by_cases h : k=0
      · subst k
        have bounded : F.card ≤ 3 := size
        simpa using (show F.card ≤ 13 by omega)
      by_cases h' : k=1
      · subst k
        have eq : (Finset.univ.filter (fun i : Fin n => (if i ∈ F then 0 else 1) = 1)) = Fᶜ := by
          ext i; by_cases hi : i ∈ F <;> simp [hi]
        rw [eq,Finset.card_compl,Fintype.card_fin]
        exact rest
      · have no (i : Fin n) : (if i ∈ F then 0 else 1) ≠ k := by split <;> omega
        simp [no]
    · intro x y diff i hi j hj
      change block (c G x x) ≠ block (c G y y) at diff
      rw [atPoint,atPoint] at diff
      by_cases hx : x ∈ F <;> by_cases hy : y ∈ F <;> simp only [hx,hy,if_true,if_false] at diff
      · exact (diff rfl).elim
      · rw [sameFiber hx] at hi
        exact transpose _ ((uniform y hy j hj i hi).trans (uniform y hy y ((member G _ _).mpr rfl) x hx).symm)
      · rw [sameFiber hy] at hj
        exact (uniform x hx i hi j hj).trans (uniform x hx x ((member G _ _).mpr rfl) y hy).symm
      · exact (diff rfl).elim
  · push_neg at uniform
    obtain ⟨a,ha,i,hi,j,hj,neq⟩ := uniform
    obtain ⟨x,hx,y,hy,single⟩ := single_row G a b size ⟨i,hi,j,hj,neq⟩
    have fy := sameFiber hy
    have outside : x ∉ fiber G y := by
      rw [fy]
      exact fun bad => ha ((member G _ _).mpr (((member G _ _).mp hx).symm.trans ((member G _ _).mp bad)))
    exact SmallUnion.erase_of_column_one p x y outside (fy.symm ▸ pos) (fy.symm ▸ rest) single

theorem isomorphic_of_three {G H : Graph 16} (b : Fin 16) (size : (fiber G b).card = 3)
    (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,g,ip,_,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  obtain ⟨e,he⟩ := realize p b (by omega) (by omega) (by omega)
  exact ⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => StrategyColorLaws.common_edge p (he i j)⟩

end QGI.Coherent.SmallFiberElimination
