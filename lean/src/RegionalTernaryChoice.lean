import SmallVectorRealize
import RegionalPins

noncomputable section
namespace QGI.Coherent.RegionalTernaryChoice
open scoped InnerProductSpace
open FourTwelveFunctional (source)
open Synchrony Intertwiner StrategyColorLaws LargeFourteenRegion SmallUnion
open Classical

variable {n k : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {reg : Nat → Prop} {f g : Fin k → Fin n}
    (D : DataFor p reg f g)

include D

theorem vector_data (ξ : cyclic p) (nz : ξ≠0) :
    SmallVectorCells.Data ξ (fun i a => U p (f i) (g a) ξ) (fun i j => source G (f i) (f j))
      (fun a b => targetName p (g a) (g b)) := by
  have allRow (i) : ∑ a, U p (f i) a ξ=ξ := by
    apply Subtype.ext
    change (cyclic p).subtype (∑ a, U p (f i) a ξ)=_
    rw [map_sum]; exact (magic_sums p (f i) ξ).1
  have allCol (a) : ∑ i, U p i (g a) ξ=ξ := by
    apply Subtype.ext
    change (cyclic p).subtype (∑ i, U p i (g a) ξ)=_
    rw [map_sum]; exact (magic_sums p (g a) ξ).2
  refine ⟨nz,?_,?_,?_,?_,fun _ _ _ _ h => RegionalBinaryChoice.orthogonal p ξ h⟩
  · intro i; refine Eq.trans ?_ (allRow i)
    apply Fintype.sum_of_injective g D.injG _ (fun a => U p (f i) a ξ) _ (fun _ => rfl)
    intro a no
    by_contra h
    have eq : source G (f i) (f i)=targetName p a a := DoubledEdges.diag_of_nonzero p h
    exact no ((D.tgt _).mpr ((congrArg reg eq).mp ((D.src _).mp ⟨i,rfl⟩)))
  · intro a; refine Eq.trans ?_ (allCol a)
    apply Fintype.sum_of_injective f D.injF _ (fun i => U p i (g a) ξ) _ (fun _ => rfl)
    intro i no
    by_contra h
    have eq : source G i i=targetName p (g a) (g a) := DoubledEdges.diag_of_nonzero p h
    exact no ((D.src _).mpr ((congrArg reg eq).mpr ((D.tgt _).mp ⟨a,rfl⟩)))
  · intro i a b ne
    apply RegionalBinaryChoice.orthogonal
    intro name
    have diag := entries p name (closure H).one_mem (initial_diagonal p)
    simp [Matrix.one_apply,D.injG.ne ne] at diag
  · intro a i j ne
    apply RegionalBinaryChoice.orthogonal
    intro name
    have diag := entries p name (closure H).one_mem (initial_diagonal p)
    simp [Matrix.one_apply,D.injF.ne ne] at diag

/-- A common nonzero vector restricts every row to one specified target
class, and every such class has size at most three. -/
theorem solve {S : Type*} (ξ : cyclic p) (nz : ξ≠0) (tag : Fin k → S)
    (one : ∀ i a b, U p (f i) (g a) ξ≠0 → U p (f i) (g b) ξ≠0 → tag a=tag b)
    (few : ∀ s, (Finset.univ.filter (fun i => tag i=s)).card≤3) :
    ∃ e : Equiv.Perm (Fin k), ∀ i j, source G (f i) (f j)=targetName p (g (e i)) (g (e j)) :=
  SmallVectorCells.of_target_partition (vector_data p D ξ nz) tag one few

attribute [local instance 2000] Classical.propDecidable

/-- Color signatures against the pinned points automatically give a
partition respected on every row of the same vector table. -/
theorem pins (ξ : cyclic p) (nz : ξ≠0) (J : Type*) (t : J → Fin n)
    (fixed : ∀ j, RegionalPins.Pinned p ξ (t j))
    (short : ∀ a : Fin k, (Finset.univ.filter (fun b : Fin k => targetName p (g b) (g b)=targetName p (g a) (g a) ∧
      ∀ j, targetName p (g b) (t j)=targetName p (g a) (t j))).card≤3) :
    ∃ e : Equiv.Perm (Fin k), ∀ i j, source G (f i) (f j)=targetName p (g (e i)) (g (e j)) := by
  let tag (a : Fin k) := (targetName p (g a) (g a),fun j => targetName p (g a) (t j))
  apply solve p D ξ nz tag
  · intro i a b ha hb
    exact Prod.ext ((DoubledEdges.diag_of_nonzero p ha).symm.trans (DoubledEdges.diag_of_nonzero p hb))
      (funext (fun j => RegionalPins.equal p ξ ha hb (fixed j)))
  · intro s
    by_cases used : ∃ a, tag a=s
    · obtain ⟨a,rfl⟩ := used
      apply (Finset.card_le_card ?_).trans (short a)
      intro b hb
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hb ⊢
      exact ⟨congrArg Prod.fst hb,congrFun (congrArg Prod.snd hb)⟩
    · have empty : Finset.univ.filter (fun i => tag i=s)=∅ := by
        apply Finset.eq_empty_iff_forall_not_mem.mpr
        intro i hi; simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi; exact used ⟨i,hi⟩
      rw [empty,Finset.card_empty]; exact Nat.zero_le _

theorem source_pins (ξ : cyclic p) (nz : ξ≠0) {J : Type*} (s t : J → Fin n)
    (fixed : ∀ j, U p (s j) (t j) ξ=ξ)
    (short : ∀ a : Fin k, (Finset.univ.filter (fun b : Fin k => source G (f b) (f b)=source G (f a) (f a) ∧
      ∀ j, source G (f b) (s j)=source G (f a) (s j))).card≤3) :
    ∃ e : Equiv.Perm (Fin k), ∀ i j, source G (f i) (f j)=targetName p (g (e i)) (g (e j)) := by
  let sh (a : Fin k) := (source G (f a) (f a),fun j => source G (f a) (s j))
  let th (a : Fin k) := (targetName p (g a) (g a),fun j => targetName p (g a) (t j))
  apply SmallVectorCells.of_partition (vector_data p D ξ nz) sh th
  · intro i a act
    refine Prod.ext (DoubledEdges.diag_of_nonzero p act) (funext (fun j => ?_))
    apply (associated p).mpr (StrategyColors.maps_support p ?_)
    intro zero
    have eq := congrArg (fun Z : Module.End ℂ (cyclic p) => Z ξ) zero
    change U p (f i) (g a) (U p (s j) (t j) ξ)=0 at eq
    exact act (fixed j ▸ eq)
  · intro q
    by_cases used : ∃ a, sh a=q
    · obtain ⟨a,rfl⟩ := used
      apply (Finset.card_le_card ?_).trans (short a)
      intro b hb
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hb ⊢
      exact ⟨congrArg Prod.fst hb,congrFun (congrArg Prod.snd hb)⟩
    · have empty : Finset.univ.filter (fun i => sh i=q)=∅ := by
        apply Finset.eq_empty_iff_forall_not_mem.mpr
        intro i hi; simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi; exact used ⟨i,hi⟩
      rw [empty,Finset.card_empty]; exact Nat.zero_le _

theorem root (x : Fin n)
    (short : ∀ v : Nat, (Finset.univ.filter (fun b : Fin k => source G (f b) x=v)).card≤3) :
    ∃ e : Equiv.Perm (Fin k), ∀ i j, source G (f i) (f j)=targetName p (g (e i)) (g (e j)) := by
  let ψ : cyclic p := ⟨p.psi,psi_mem p⟩
  have nz : ψ≠0 := fun h => psi_ne_zero p (congrArg Subtype.val h)
  obtain ⟨a,ha⟩ := DoubledEdges.nonzero_row p ψ nz x
  let ξ := U p x a ψ
  have fixed : U p x a ξ=ξ := congrArg (fun Z : Module.End ℂ (cyclic p) => Z ψ) (restricted_projection p _ _).1
  apply source_pins p D ξ ha (fun _ : Unit => x) (fun _ => a) (fun _ => fixed)
  intro i
  apply (Finset.card_le_card ?_).trans (short (source G (f i) x))
  intro b hb
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hb ⊢
  exact hb.2 ()

end QGI.Coherent.RegionalTernaryChoice
