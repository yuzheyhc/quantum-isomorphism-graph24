import CoherentRelations
import CoherentIntertwines

noncomputable section
open scoped BigOperators

namespace QGI.Coherent.StrategyColors
open Synchrony Intertwiner

variable {n : Nat} {G H : Graph n} {K : Type}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Exactly the numeric basic relations used in the coherent closure of G. -/
abbrev Palette (G : Graph n) := {k : Nat // ∃ i j, Relations.color (closure G) i j = k}

def label (G : Graph n) (i j : Fin n) : Palette G :=
  ⟨Relations.color (closure G) i j, i, j, rfl⟩

def indicator (G : Graph n) (k : Palette G) : Coherent.Mat n :=
  fun i j => if Relations.color (closure G) i j = k.val then 1 else 0

variable (p : PerfectStrategy G H K)

/-- A source and a target ordered pair occur together in the fixed strategy. -/
def Supported (x y a b : Fin n) : Prop := (U p x a).comp (U p y b) ≠ 0

theorem entry_eq {A B : Coherent.Mat n} (h : Intertwines p A B) {x y a b : Fin n}
    (support : Supported p x y a b) : A x y = B a b :=
  not_not.mp (fun bad => support (compatible_of_intertwines p h _ _ _ _ bad))

private theorem partial_sums (x : Fin n) (v : cyclic p) :
    (∑ a, U p x a v) = v ∧ (∑ a, U p a x v) = v := by
  constructor
  · apply Subtype.ext
    change (cyclic p).subtype (∑ a, U p x a v) = (v : K)
    rw [map_sum]; exact (magic_sums p x v).1
  · apply Subtype.ext
    change (cyclic p).subtype (∑ a, U p a x v) = (v : K)
    rw [map_sum]; exact (magic_sums p x v).2

private theorem nonzero_state : (⟨p.psi, psi_mem p⟩ : cyclic p) ≠ 0 :=
  fun e => psi_ne_zero p (congrArg (fun v : cyclic p => (v : K)) e)

private theorem zero_apply {i j a b : Fin n} (h : ¬Supported p i j a b) (v : cyclic p) :
    U p i a (U p j b v) = 0 := by
  have zero : (U p i a).comp (U p j b) = 0 := not_not.mp h
  exact congrArg (fun f : cyclic p →ₗ[ℂ] cyclic p => f v) zero

theorem exists_target (x y : Fin n) : ∃ a b, Supported p x y a b := by
  by_contra! no
  let v : cyclic p := ⟨p.psi,psi_mem p⟩
  apply nonzero_state p
  calc
    v = ∑ a, U p x a v := (partial_sums p x _).1.symm
    _ = ∑ a, ∑ b, U p x a (U p y b v) := by simp_rw [← map_sum,(partial_sums p y _).1]
    _ = 0 := by simp [fun a b => zero_apply p (no a b) v]

theorem exists_source (a b : Fin n) : ∃ x y, Supported p x y a b := by
  by_contra! no
  let v : cyclic p := ⟨p.psi,psi_mem p⟩
  apply nonzero_state p
  calc
    v = ∑ x, U p x a v := (partial_sums p a _).2.symm
    _ = ∑ x, ∑ y, U p x a (U p y b v) := by simp_rw [← map_sum,(partial_sums p b _).2]
    _ = 0 := by simp [fun x y => zero_apply p (no x y) v]

/-- The corresponding source-side algebra is generated using the same
strategy operators; it does not require choosing an inverse strategy. -/
private def sources : CoherentAlgebra n where
  space := {
    carrier := {A | ∃ B ∈ (closure H).space, Intertwines p A B}
    zero_mem' := ⟨0,(closure H).space.zero_mem,initial_full p 0⟩
    add_mem' := by
      rintro _ _ ⟨B,hB,h⟩ ⟨D,hD,g⟩
      exact ⟨B+D,(closure H).space.add_mem hB hD,entrywise₂ p (·+·) h g⟩
    smul_mem' := by
      rintro c _ ⟨B,hB,h⟩
      exact ⟨c • B,(closure H).space.smul_mem c hB,entrywise₂ p (fun x _ => c • x) h h⟩ }
  one_mem := ⟨1,(closure H).one_mem,initial_diagonal p⟩
  ones_mem := ⟨ones n,(closure H).ones_mem,initial_full p 1⟩
  mul_mem := by
    rintro _ _ ⟨B,hB,h⟩ ⟨D,hD,g⟩
    exact ⟨B*D,(closure H).mul_mem hB hD,matrix_mul p h g⟩
  schur_mem := by
    rintro _ _ ⟨B,hB,h⟩ ⟨D,hD,g⟩
    exact ⟨schur B D,(closure H).schur_mem hB hD,hadamard p h g⟩
  adjoint_mem := by
    rintro _ ⟨B,hB,h⟩
    exact ⟨B.conjTranspose,(closure H).adjoint_mem hB,conjugate_transpose p h⟩

theorem exists_mem_intertwining_target {A : Coherent.Mat n} (hA : A ∈ (closure G).space) :
    ∃ B ∈ (closure H).space, Intertwines p A B :=
  hA (sources p) ⟨adjacency H, adjacency_mem H, initial_adjacency p⟩

theorem same_iff {x y a b u v c d : Fin n} (h : Supported p x y a b)
    (g : Supported p u v c d) : label G x y = label G u v ↔ label H a b = label H c d := by
  simp only [label,Subtype.mk.injEq,Relations.same]
  constructor
  · intro eq B hB
    obtain ⟨A,hA,hAB⟩ := exists_mem_intertwines_of_mem_closure p hB
    exact (entry_eq p hAB h).symm.trans ((eq A hA).trans (entry_eq p hAB g))
  · intro eq A hA
    obtain ⟨B,hB,hAB⟩ := exists_mem_intertwining_target p hA
    exact (entry_eq p hAB h).trans ((eq B hB).trans (entry_eq p hAB g).symm)

private def Paired (k : Palette G) (l : Palette H) : Prop :=
  ∃ x y a b, label G x y = k ∧ label H a b = l ∧ Supported p x y a b

private theorem right_total (k : Palette G) : ∃ l, Paired p k l := by
  obtain ⟨i,j,h⟩ := k.property
  obtain ⟨a,b,s⟩ := exists_target p i j
  exact ⟨label H a b,i,j,a,b,Subtype.ext h,rfl,s⟩

private theorem left_total (l : Palette H) : ∃ k, Paired p k l := by
  obtain ⟨a,b,h⟩ := l.property
  obtain ⟨i,j,s⟩ := exists_source p a b
  exact ⟨label G i j,i,j,a,b,rfl,Subtype.ext h,s⟩

private theorem pair_eq {k k' : Palette G} {l l' : Palette H} (h : Paired p k l)
    (g : Paired p k' l') : k = k' ↔ l = l' := by
  obtain ⟨x,y,a,b,rfl,rfl,s⟩ := h
  obtain ⟨i,j,c,d,rfl,rfl,t⟩ := g
  exact same_iff p s t

/-- The single correspondence of used colors forced by the given strategy. -/
def equiv : Palette G ≃ Palette H where
  toFun k := (right_total p k).choose
  invFun l := (left_total p l).choose
  left_inv k := (pair_eq p (left_total p _).choose_spec (right_total p k).choose_spec).mpr rfl
  right_inv l := (pair_eq p (right_total p _).choose_spec (left_total p l).choose_spec).mp rfl

theorem maps_support {x y a b : Fin n} (h : Supported p x y a b) :
    equiv p (label G x y) = label H a b :=
  (pair_eq p (right_total p _).choose_spec ⟨x,y,a,b,rfl,rfl,h⟩).mp rfl

theorem intertwines_indicator (k : Palette G) :
    Intertwines p (indicator G k) (indicator H (equiv p k)) := by
  apply intertwines_of_compatible p
  intro i j a b mismatch
  by_contra support
  have h := maps_support p support
  have iffColor : Relations.color (closure G) i j = k.val ↔
      Relations.color (closure H) a b = (equiv p k).val := by
    change (label G i j).val = k.val ↔ (label H a b).val = (equiv p k).val
    rw [Subtype.val_inj,Subtype.val_inj,←h,(equiv p).injective.eq_iff]
  exact mismatch (by simp only [indicator,iffColor])

end QGI.Coherent.StrategyColors