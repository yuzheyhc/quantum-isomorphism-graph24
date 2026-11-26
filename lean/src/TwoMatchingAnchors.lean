import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace QGI.Coherent.TwoMatchingAnchors

/-- Two disjoint perfect matchings on eight vertices generate at most two
orbits. A property closed under both matchings is determined by two anchors. -/
theorem determine (P Q : Fin 8 → Fin 8) (pinv : Function.Involutive P) (qinv : Function.Involutive Q)
    (pfree : ∀ i, P i ≠ i) (qfree : ∀ i, Q i ≠ i) (apart : ∀ i, P i ≠ Q i) :
    ∃ a b, ∀ E : Fin 8 → Prop, E a → E b → (∀ i, E i → E (P i)) →
      (∀ i, E i → E (Q i)) → ∀ i, E i := by
  classical
  let R := fun x y : Fin 8 => P x = y ∨ Q x = y
  let orbit := fun x => Finset.univ.filter (Relation.EqvGen R x)
  have mem (x y) : y ∈ orbit x ↔ Relation.EqvGen R x y := by simp [orbit]
  have size (x) : 4 ≤ (orbit x).card := by
    have px : Relation.EqvGen R x (P x) := .rel _ _ (Or.inl rfl)
    have qx : Relation.EqvGen R x (Q x) := .rel _ _ (Or.inr rfl)
    have pqx : Relation.EqvGen R x (P (Q x)) := .trans _ _ _ qx (.rel _ _ (Or.inl rfl))
    let s : Finset (Fin 8) := {x, P x, Q x, P (Q x)}
    have other : x ≠ P (Q x) := fun h => apart x ((congrArg P h).trans (pinv (Q x)))
    have ds : s.card = 4 := by
      simp [s,Finset.card_insert_of_not_mem,(pfree x).symm,(qfree x).symm,other,apart x,
        pinv.injective.ne (qfree x).symm,(pfree (Q x)).symm]
    rw [← ds]
    apply Finset.card_le_card
    intro y hy
    simp only [s,Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact (mem _ _).mpr (.refl _)
    · exact (mem _ _).mpr px
    · exact (mem _ _).mpr qx
    · exact (mem _ _).mpr pqx
  have transport {E : Fin 8 → Prop} (hp : ∀ i, E i → E (P i)) (hq : ∀ i, E i → E (Q i))
      {i j} (h : Relation.EqvGen R i j) : E i ↔ E j := by
    induction h with
    | rel x y h =>
      rcases h with rfl | rfl
      · exact ⟨hp x,fun e => pinv x ▸ hp (P x) e⟩
      · exact ⟨hq x,fun e => qinv x ▸ hq (Q x) e⟩
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h k => exact h.trans k
  by_cases all : ∀ i, i ∈ orbit 0
  · exact ⟨0,0,fun _ h _ hp hq i => (transport hp hq ((mem _ _).mp (all i))).mp h⟩
  push_neg at all
  obtain ⟨b,hb⟩ := all
  have disjoint : Disjoint (orbit 0) (orbit b) := Finset.disjoint_left.mpr (fun x hx hy =>
    hb ((mem _ _).mpr (.trans _ _ _ ((mem _ _).mp hx) (.symm _ _ ((mem _ _).mp hy)))))
  have un : orbit 0 ∪ orbit b = Finset.univ := Finset.eq_univ_of_card _ (by
    have top := Finset.card_le_univ (orbit 0 ∪ orbit b)
    rw [Finset.card_union_of_disjoint disjoint] at top ⊢
    have t := size 0
    have u := size b
    simp only [Fintype.card_fin] at top ⊢
    omega)
  refine ⟨0,b,fun E e f hp hq i => ?_⟩
  have hi : i ∈ orbit 0 ∪ orbit b := un ▸ Finset.mem_univ i
  rcases Finset.mem_union.mp hi with hi | hi
  · exact (transport hp hq ((mem _ _).mp hi)).mp e
  · exact (transport hp hq ((mem _ _).mp hi)).mp f

end QGI.Coherent.TwoMatchingAnchors
