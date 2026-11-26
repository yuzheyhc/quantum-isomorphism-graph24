import TernaryVectorChoice
import Mathlib.Logic.Relation

noncomputable section
namespace QGI.SmallVectorCells
open scoped InnerProductSpace
variable {E X Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [Fintype X] [Fintype Y]

structure Data (ξ : E) (u : X → Y → E) (c : X → X → Nat) (d : Y → Y → Nat) : Prop where
  nz : ξ≠0
  row : ∀ i, ∑ a, u i a=ξ
  col : ∀ a, ∑ i, u i a=ξ
  ro : ∀ i a b, a≠b → ⟪u i a,u i b⟫_ℂ=0
  co : ∀ a i j, i≠j → ⟪u i a,u j a⟫_ℂ=0
  bad : ∀ i j a b, c i j≠d a b → ⟪u i a,u j b⟫_ℂ=0

def linked (u : X → Y → E) : X ⊕ Y → X ⊕ Y → Prop
  | .inl i,.inr a => u i a≠0
  | _,_ => False

abbrev Component (u : X → Y → E) := Quot (linked u)
def left (u : X → Y → E) (i : X) : Component u := Quot.mk _ (.inl i)
def right (u : X → Y → E) (a : Y) : Component u := Quot.mk _ (.inr a)
theorem edge {u : X → Y → E} {i a} (h : u i a≠0) : left u i=right u a := Quot.sound h

/-- A pair of functions agreeing on every nonzero entry is a single function
of the bipartite support component. -/
theorem constant_on_component {u : X → Y → E} {α : Type*} (f : X → α) (g : Y → α)
    (match' : ∀ i a, u i a≠0 → f i=g a) :
    ∃ h : Component u → α, (∀ i, h (left u i)=f i) ∧ ∀ a, h (right u a)=g a := by
  let f' := Sum.elim f g
  have descend (s t : X ⊕ Y) (rel : linked u s t) : f' s=f' t := by
    cases s with
    | inr => cases t <;> contradiction
    | inl i =>
      cases t with
      | inl => contradiction
      | inr a => exact match' i a rel
  exact ⟨Quot.lift f' descend,fun _ => rfl,fun _ => rfl⟩

private theorem count_mass (P : X → Y → ℂ) (S : Finset X) (T : Finset Y) (w : ℂ) (nz : w≠0)
    (row : ∀ i, ∑ a, P i a=w) (col : ∀ a, ∑ i, P i a=w)
    (compat : ∀ i a, P i a≠0 → (i∈S ↔ a∈T)) : S.card=T.card := by
  classical
  have row' (i) (hi : i∈S) : ∑ a∈T, P i a=w := by
    rw [←row i]
    exact Finset.sum_subset (Finset.subset_univ _) (fun a _ no => by by_contra nonzero; exact no ((compat i a nonzero).mp hi))
  have col' (a) (ha : a∈T) : ∑ i∈S, P i a=w := by
    rw [←col a]
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ no => by by_contra nonzero; exact no ((compat i a nonzero).mpr ha))
  have eq : (S.card : ℂ)*w=(T.card : ℂ)*w := calc
    _ = ∑ i∈S, ∑ a∈T, P i a := by rw [Finset.sum_congr rfl row',Finset.sum_const,nsmul_eq_mul]
    _ = ∑ a∈T, ∑ i∈S, P i a := Finset.sum_comm
    _ = _ := by rw [Finset.sum_congr rfl col',Finset.sum_const,nsmul_eq_mul]
  exact_mod_cast mul_right_cancel₀ nz eq

variable {ξ : E} {u : X → Y → E} {c : X → X → Nat} {d : Y → Y → Nat} (D : Data ξ u c d)

include D

theorem self_mass {i a} (nz : u i a≠0) : ⟪u i a,ξ⟫_ℂ≠0 := by
  rw [←D.row i,inner_sum,Finset.sum_eq_single a]
  · exact fun h => nz (inner_self_eq_zero.mp h)
  · exact fun b _ h => D.ro i a b h.symm
  · simp

open Classical in
theorem same_size (s : Component u) : (Finset.univ.filter (fun i => left u i=s)).card =
    (Finset.univ.filter (fun a => right u a=s)).card := by
  let P := fun i a => ⟪ξ,u i a⟫_ℂ
  apply count_mass P _ _ ⟪ξ,ξ⟫_ℂ (fun h => D.nz (inner_self_eq_zero.mp h))
  · intro i; simpa only [P,←inner_sum,D.row]
  · intro a; simpa only [P,←inner_sum,D.col]
  · intro i a h
    have nz : u i a≠0 := fun z => h (by simp [P,z])
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,edge nz]

open Classical in
theorem degrees (s : Component u) (v : Nat) :
    ∃ h : Component u → Nat,
      (∀ i, h (left u i)=(Finset.univ.filter (fun j => left u j=s ∧ c i j=v)).card) ∧
      ∀ a, h (right u a)=(Finset.univ.filter (fun b => right u b=s ∧ d a b=v)).card := by
  apply constant_on_component
  intro i a nz
  let P := fun j b => ⟪u i a,u j b⟫_ℂ
  apply count_mass P _ _ ⟪u i a,ξ⟫_ℂ (self_mass D nz)
  · intro j; simpa only [P,←inner_sum,D.row]
  · intro b; simpa only [P,←inner_sum,D.col]
  · intro j b h
    have nonzero : u j b≠0 := fun z => h (by simp [P,z])
    have color : c i j=d a b := of_not_not fun ne => h (D.bad i j a b ne)
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,edge nonzero,color]

open Classical in
/-- Incoming colors have the same degree on the same support components. -/
theorem indegrees (s : Component u) (v : Nat) :
    ∃ h : Component u → Nat,
      (∀ i, h (left u i)=(Finset.univ.filter (fun j => left u j=s ∧ c j i=v)).card) ∧
      ∀ a, h (right u a)=(Finset.univ.filter (fun b => right u b=s ∧ d b a=v)).card := by
  have rev : Data ξ u (fun i j => c j i) (fun a b => d b a) := { D with
    bad := fun i j a b ne => inner_eq_zero_symm.mp (D.bad j i b a ne) }
  exact degrees rev s v

end QGI.SmallVectorCells
