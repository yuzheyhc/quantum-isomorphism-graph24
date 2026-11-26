import SmallVectorCells

namespace QGI.SmallTableMatching

def one {X Y : Type*} (p : X → Y → Bool) (v : Bool) : Prop :=
  (∀ i, ∃! j, p i j=v) ∧ ∀ j, ∃! i, p i j=v

def regular {X Y : Type*} [Fintype X] [Fintype Y] (p : X → Y → Bool) : Prop :=
  (∀ i j, (Finset.univ.filter (fun a => p i a=true)).card=(Finset.univ.filter (fun a => p j a=true)).card) ∧
  ∀ a b, (Finset.univ.filter (fun i => p i a=true)).card=(Finset.univ.filter (fun i => p i b=true)).card

instance {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] (p : X → Y → Bool) (v : Bool) :
    Decidable (one p v) := by unfold one ExistsUnique; infer_instance
instance {X Y : Type*} [Fintype X] [Fintype Y] (p : X → Y → Bool) :
    Decidable (regular p) := by unfold regular; infer_instance

/-- On at most three points per side, a nonconstant biregular Boolean
rectangle, or its complement, is a bijection. -/
theorem finite_masks {k m : Nat} (hk : k≤3) (hm : m≤3) (p : Fin k → Fin m → Bool) (reg : regular p) :
    (∃ b, ∀ i j, p i j=b) ∨ ∃ b, one p b := by
  revert p
  interval_cases k <;> interval_cases m <;> native_decide

private theorem lift_one {A B : Type*} (e : A ≃ B) (P : B → Prop) (h : ∃! i, P (e i)) : ∃! b, P b := by
  obtain ⟨i,hi,only⟩ := h
  exact ⟨e i,hi,fun b hb => by obtain ⟨a,rfl⟩ := e.surjective b; exact congrArg e (only a hb)⟩

open Classical in
theorem masks {X Y : Type*} [Fintype X] [Fintype Y] (hx : Fintype.card X≤3) (hy : Fintype.card Y≤3)
    (p : X → Y → Bool) (reg : regular p) : (∃ b, ∀ i j, p i j=b) ∨ ∃ b, one p b := by
  let f := (Fintype.equivFin X).symm
  let g := (Fintype.equivFin Y).symm
  let q := fun i j => p (f i) (g j)
  have row i : (Finset.univ.filter (fun j => q i j=true)).card=(Finset.univ.filter (fun a => p (f i) a=true)).card := by
    rw [←Finset.card_map g.toEmbedding]
    congr 1
    ext x
    simp [q]
  have col j : (Finset.univ.filter (fun i => q i j=true)).card=(Finset.univ.filter (fun a => p a (g j)=true)).card := by
    rw [←Finset.card_map f.toEmbedding]
    congr 1
    ext x
    simp [q]
  have hreg : regular q := ⟨fun i j => ((row i).trans (reg.1 _ _)).trans (row j).symm,
    fun i j => ((col i).trans (reg.2 _ _)).trans (col j).symm⟩
  rcases finite_masks hx hy q hreg with ⟨v,h⟩|⟨v,hr,hc⟩
  · exact Or.inl ⟨v,fun i j => by simpa [q] using h (f.symm i) (g.symm j)⟩
  · exact Or.inr ⟨v,fun i => by obtain ⟨i,rfl⟩ := f.surjective i; exact lift_one g (fun a => p (f i) a=v) (hr i),
      fun j => by obtain ⟨j,rfl⟩ := g.surjective j; exact lift_one f (fun a => p a (g j)=v) (hc j)⟩

noncomputable def equivOfOne {X Y : Type*} (p : X → Y → Bool) (v : Bool) (h : one p v) : X ≃ Y where
  toFun i := (h.1 i).exists.choose
  invFun j := (h.2 j).exists.choose
  left_inv i := (h.2 _).unique (h.2 _).exists.choose_spec (h.1 i).exists.choose_spec
  right_inv j := (h.1 _).unique (h.1 _).exists.choose_spec (h.2 j).exists.choose_spec

theorem marks {X Y : Type*} {p : X → Y → Bool} {v : Bool} (h : one p v) (i : X) (j : Y) :
    p i j=v ↔ equivOfOne p v h i=j :=
  ⟨fun hj => (h.1 i).unique (h.1 i).exists.choose_spec hj,fun eq => eq ▸ (h.1 i).exists.choose_spec⟩

end QGI.SmallTableMatching
