import StrategyColorLaws

noncomputable section
namespace QGI.Coherent.SplitRectangle
open StrategyColorLaws

variable {L R : Type} [Fintype L] [Fintype R]
abbrev Table (L R : Type) := (L ⊕ R) → (L ⊕ R) → Nat

def Products (c d : Table L R) : Prop :=
  ∀ {i j x y}, c i j = d x y → ∀ a b, count c a b i j = count d a b x y

private theorem middle {c d : Table L R} (law : Products c d) {i j x y}
    (h : c i j = d x y) (k : L ⊕ R) : ∃ z, c i k = d x z ∧ c k j = d z y := by
  classical
  have counts := law h (c i k) (c k j)
  simp only [count,Finset.sum_boole] at counts
  have pos := Finset.card_pos.mpr (show (Finset.univ.filter
    (fun z => c i z = c i k ∧ c z j = c k j)).Nonempty from
    ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl,rfl⟩⟩)
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (pos.trans_eq counts)
  exact ⟨z,(Finset.mem_filter.mp hz).2.1.symm,(Finset.mem_filter.mp hz).2.2.symm⟩

/-- In one cross rectangle, agreeing in a column forces two entire rows to
agree, and dually for columns. This includes a uniform rectangle and one
colored by agreement of two binary half labels. -/
def Twins (B : L → R → Nat) : Prop :=
  (∀ i x j, B i j = B x j → ∀ y, B i y = B x y) ∧
  (∀ i j y, B i j = B i y → ∀ x, B x j = B x y)

omit [Fintype L] [Fintype R] in
theorem twins_of_halves (left : L → Bool) (right : R → Bool) (v w : Nat) :
    Twins (fun i j => if left i = right j then v else w) := by
  constructor
  · intro i x j h y
    cases a : left i <;> cases b : left x <;> cases s : right j <;> cases t : right y <;> simp_all
  · intro i j y h x
    cases a : left i <;> cases b : left x <;> cases s : right j <;> cases t : right y <;> simp_all

/-- One exterior column distinguishes the source row types, and one
entry distinguishes the column types that contain the chosen color. -/
def AtAnchor (B : L → R → Nat) (i₀ : L) (j₀ : R) : Prop :=
  (∀ i x, B i j₀ = B x j₀ → ∀ y, B i y = B x y) ∧
  (∀ y, B i₀ j₀ = B i₀ y → ∀ x, B x j₀ = B x y)

theorem at_anchor (c d : Table L R) (i₀ : L) (j₀ : R)
    (rect : ∀ {i j x y}, c i j = c x y → (i.isLeft,j.isLeft) = (x.isLeft,y.isLeft))
    (rev : ∀ {i j x y}, c i j = c x y → c j i = c y x)
    (transpose : ∀ {i j x y}, c i j = d x y → c j i = d y x)
    (products : Products c d) (anchor : AtAnchor (fun i j => c (.inl i) (.inr j)) i₀ j₀)
    (left : ∀ x, ∃ l : Equiv.Perm L, l i₀ = x ∧
      ∀ i j, c (.inl i) (.inl j) = d (.inl (l i)) (.inl (l j)))
    (r : Equiv.Perm R) (right : ∀ i j, c (.inr i) (.inr j) = d (.inr (r i)) (.inr (r j))) :
    ∃ e : Equiv.Perm (L ⊕ R), ∀ i j, c i j = d (e i) (e j) := by
  have back : Products d c := fun h a b => (products h.symm a b).symm
  obtain ⟨z,_,cross⟩ := middle products (right j₀ j₀) (.inl i₀)
  cases z with
  | inr y =>
    obtain ⟨j,rfl⟩ := r.surjective y
    have bad := rect (cross.trans (right j j₀).symm)
    cases bad
  | inl x =>
    obtain ⟨l,base,leftIso⟩ := left x
    rw [←base] at cross
    have column (i : L) : c (.inl i) (.inr j₀) = d (.inl (l i)) (.inr (r j₀)) := by
      obtain ⟨k,h₁,h₂⟩ := middle back (leftIso i₀ i).symm (.inr (r j₀))
      cases k with
      | inl y => cases rect (cross.trans h₁)
      | inr y =>
        have eq := anchor.2 y (cross.trans h₁) i
        exact transpose ((rev eq).trans h₂.symm)
    have allCross (i : L) (j : R) : c (.inl i) (.inr j) = d (.inl (l i)) (.inr (r j)) := by
      obtain ⟨k,h₁,h₂⟩ := middle back (right j₀ j).symm (.inl (l i))
      cases k with
      | inr y => cases rect ((transpose (column i)).trans h₁)
      | inl y =>
        have eq := rev ((transpose (column i)).trans h₁)
        exact (anchor.1 i y eq j).trans h₂.symm
    refine ⟨Equiv.sumCongr l r,?_⟩
    rintro (i|i) (j|j)
    · exact leftIso i j
    · exact allCross i j
    · exact transpose (allCross j i)
    · exact right i j

/-- If one source cross rectangle has the twin property, independently
realized shores can be synchronized by prescribing one point on the left.
There is no shape hypothesis on the target cross rectangle. -/
theorem realize (c d : Table L R) (i₀ : L) (j₀ : R)
    (rect : ∀ {i j x y}, c i j = c x y → (i.isLeft,j.isLeft) = (x.isLeft,y.isLeft))
    (rev : ∀ {i j x y}, c i j = c x y → c j i = c y x)
    (transpose : ∀ {i j x y}, c i j = d x y → c j i = d y x)
    (products : Products c d) (twins : Twins (fun i j => c (.inl i) (.inr j)))
    (left : ∀ x, ∃ l : Equiv.Perm L, l i₀ = x ∧
      ∀ i j, c (.inl i) (.inl j) = d (.inl (l i)) (.inl (l j)))
    (r : Equiv.Perm R) (right : ∀ i j, c (.inr i) (.inr j) = d (.inr (r i)) (.inr (r j))) :
    ∃ e : Equiv.Perm (L ⊕ R), ∀ i j, c i j = d (e i) (e j) :=
  at_anchor c d i₀ j₀ rect rev transpose products
    ⟨fun i x => twins.1 i x j₀,fun y => twins.2 i₀ j₀ y⟩ left r right

theorem realize_either (c d : Table L R) (i₀ : L) (j₀ : R)
    (rc : ∀ {i j x y}, c i j = c x y → (i.isLeft,j.isLeft) = (x.isLeft,y.isLeft))
    (rd : ∀ {i j x y}, d i j = d x y → (i.isLeft,j.isLeft) = (x.isLeft,y.isLeft))
    (tc : ∀ {i j x y}, c i j = c x y → c j i = c y x)
    (td : ∀ {i j x y}, d i j = d x y → d j i = d y x)
    (tr : ∀ {i j x y}, c i j = d x y → c j i = d y x)
    (prod : Products c d)
    (twins : Twins (fun i j => c (.inl i) (.inr j)) ∨ Twins (fun i j => d (.inl i) (.inr j)))
    (left : ∀ u v, ∃ l : Equiv.Perm L, l u = v ∧
      ∀ i j, c (.inl i) (.inl j) = d (.inl (l i)) (.inl (l j)))
    (r : Equiv.Perm R) (right : ∀ i j, c (.inr i) (.inr j) = d (.inr (r i)) (.inr (r j))) :
    ∃ e : Equiv.Perm (L ⊕ R), ∀ i j, c i j = d (e i) (e j) := by
  rcases twins with h | h
  · exact realize c d i₀ j₀ rc tc tr prod h (left i₀) r right
  · obtain ⟨e,he⟩ := realize d c i₀ j₀ rd td (fun eq => (tr eq.symm).symm)
      (fun eq a b => (prod eq.symm a b).symm) h (fun x => by
        obtain ⟨f,hf,iso⟩ := left x i₀
        exact ⟨f.symm,f.symm_apply_eq.mpr hf.symm,fun i j => by simpa using (iso (f.symm i) (f.symm j)).symm⟩)
      r.symm (fun i j => by simpa using (right (r.symm i) (r.symm j)).symm)
    exact ⟨e.symm,fun i j => by simpa using (he (e.symm i) (e.symm j)).symm⟩

end QGI.Coherent.SplitRectangle
