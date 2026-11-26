import SmallVectorCells

noncomputable section
namespace QGI.SmallVectorOrbits
open scoped InnerProductSpace

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {A B : I → Type*} (u : ∀ s, A s → B s → E)

def Related (s t : I) : Prop := ∃ (f : A s ≃ A t) (g : B s ≃ B t),
  ∀ i a, u s i a=u t (f i) (g a)

def tables : Setoid I where
  r := Related u
  iseqv := {
    refl := fun s => ⟨Equiv.refl _,Equiv.refl _,fun _ _ => rfl⟩
    symm := by
      rintro s t ⟨f,g,h⟩
      exact ⟨f.symm,g.symm,fun i a => by simpa only [Equiv.apply_symm_apply] using (h (f.symm i) (g.symm a)).symm⟩
    trans := by
      rintro s t r ⟨f,g,h⟩ ⟨f',g',h'⟩
      exact ⟨f.trans f',g.trans g',fun i a => (h i a).trans (h' _ _)⟩ }

/-- Synchronized choices also work for different table sizes. Related
tables use vectors selected in one representative of their orbit. -/
theorem synchronize
    (loc : ∀ s, ∃ e : A s ≃ B s, ∀ i j, ⟪u s i (e i),u s j (e j)⟫_ℂ≠0) :
    ∃ e : ∀ s, A s ≃ B s, ∀ s t, Related u s t → ∀ i j, ⟪u s i (e s i),u t j (e t j)⟫_ℂ≠0 := by
  classical
  let Q := Quotient (tables u)
  let key : I → Q := Quotient.mk _
  let rep (q : Q) : I := q.out
  choose base hb using loc
  let picked (q : Q) : Set E := Set.range (fun i => u (rep q) i (base (rep q) i))
  have good (q : Q) (x y : E) (hx : x∈picked q) (hy : y∈picked q) : ⟪x,y⟫_ℂ≠0 := by
    obtain ⟨i,rfl⟩ := hx
    obtain ⟨j,rfl⟩ := hy
    exact hb _ i j
  have lift (s : I) : Related u (rep (key s)) s := Quotient.exact (Quotient.out_eq (key s))
  choose f g h using lift
  let e (s : I) := (f s).symm.trans ((base (rep (key s))).trans (g s))
  have mem (s : I) (i : A s) : u s i (e s i)∈picked (key s) := by
    obtain ⟨i,rfl⟩ := (f s).surjective i
    exact ⟨i,by simpa only [e,Equiv.trans_apply,Equiv.symm_apply_apply] using h s i (base _ i)⟩
  refine ⟨e,fun s t rel i j => ?_⟩
  have same : key s=key t := Quotient.sound rel
  exact good (key t) _ _ (same ▸ mem s i) (mem t j)

theorem local_fin {k : Nat} (hk : k≤3) (ξ : E) (nz : ξ≠0) (w : Fin k → Fin k → E)
    (rows : ∀ i, ∑ a, w i a=ξ) (cols : ∀ a, ∑ i, w i a=ξ)
    (ro : ∀ i a b, a≠b → ⟪w i a,w i b⟫_ℂ=0) (co : ∀ a i j, i≠j → ⟪w i a,w j a⟫_ℂ=0) :
    ∃ e : Equiv.Perm (Fin k), ∀ i j, ⟪w i (e i),w j (e j)⟫_ℂ≠0 := by
  interval_cases k
  · exact ⟨Equiv.refl _,fun i => Fin.elim0 i⟩
  · refine ⟨Equiv.refl _,fun i j => ?_⟩
    fin_cases i; fin_cases j
    have val : w 0 0=ξ := by simpa using rows 0
    change ⟪w 0 0,w 0 0⟫_ℂ≠0
    rw [val]; exact fun h => nz (inner_self_eq_zero.mp h)
  · obtain ⟨x,which,_,pair⟩ := BinaryVectorChoice.exists_selection (𝕜:=ℂ) ξ nz (fun i => w i 0) (fun i => w i 1)
      (fun i => by simpa only [Fin.sum_univ_two] using rows i) (fun i => ro i 0 1 (by decide))
    have each (i : Fin 2) : ∃ a, x i=w i a := (which i).elim (fun h => ⟨0,h⟩) (fun h => ⟨1,h⟩)
    choose f eq using each
    have inj : Function.Injective f := by
      intro i j same
      by_contra ne
      apply pair i j
      rw [eq,eq,same]; exact co _ _ _ ne
    exact ⟨Equiv.ofBijective f ⟨inj,Finite.surjective_of_injective inj⟩,fun i j => by
      change ⟪w i (f i),w j (f j)⟫_ℂ≠0; simpa only [←eq] using pair i j⟩
  · exact TernaryVectorChoice.local_choice ξ nz w rows cols ro co

theorem local_small {X Y : Type*} [Fintype X] [Fintype Y] (hx : Fintype.card X≤3) (eq : Fintype.card X=Fintype.card Y)
    (ξ : E) (nz : ξ≠0) (v : X → Y → E) (rows : ∀ i, ∑ a, v i a=ξ) (cols : ∀ a, ∑ i, v i a=ξ)
    (ro : ∀ i a b, a≠b → ⟪v i a,v i b⟫_ℂ=0) (co : ∀ a i j, i≠j → ⟪v i a,v j a⟫_ℂ=0) :
    ∃ e : X ≃ Y, ∀ i j, ⟪v i (e i),v j (e j)⟫_ℂ≠0 := by
  let f := (Fintype.equivFin X).symm
  let g := (finCongr eq).trans (Fintype.equivFin Y).symm
  obtain ⟨e,he⟩ := local_fin hx ξ nz (fun i a => v (f i) (g a))
    (fun i => (g.sum_comp _).trans (rows _)) (fun a => (f.sum_comp _).trans (cols _))
    (fun i a b h => ro _ _ _ (g.injective.ne h)) (fun a i j h => co _ _ _ (f.injective.ne h))
  refine ⟨f.symm.trans (e.trans g),fun i j => ?_⟩
  obtain ⟨i,rfl⟩ := f.surjective i
  obtain ⟨j,rfl⟩ := f.surjective j
  simpa only [Equiv.trans_apply,Equiv.symm_apply_apply] using he i j

end QGI.SmallVectorOrbits
