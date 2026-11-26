import SmallShoreRealization
import SplitRectangleGluing

noncomputable section
namespace QGI.Coherent.TwoShore
open StrategyColorLaws

variable {n a b : Nat} {G H : Graph n} {K : Type}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

abbrev Points (a b : Nat) := Fin a ⊕ Fin b

/-- Coordinates on two fibers with the same names on both graphs. -/
structure Named (c : Fin n → Fin n → Nat) (a b l r : Nat) where
  e : Points a b ≃ Fin n
  left : ∀ z, (∃ i : Fin a, e (.inl i) = z) ↔ c z z = l
  right : ∀ z, (∃ j : Fin b, e (.inr j) = z) ↔ c z z = r

private theorem side_eq {c : Fin n → Fin n → Nat} {l r : Nat} (S : Named c a b l r)
    {i j : Points a b} (h : c (S.e i) (S.e i) = c (S.e j) (S.e j)) : i.isLeft = j.isLeft := by
  cases i with
  | inl i =>
    obtain ⟨x,hx⟩ := (S.left _).mpr (h.symm.trans ((S.left _).mp ⟨i,rfl⟩))
    rw [← S.e.injective hx]
    rfl
  | inr i =>
    obtain ⟨x,hx⟩ := (S.right _).mpr (h.symm.trans ((S.right _).mp ⟨i,rfl⟩))
    rw [← S.e.injective hx]
    rfl

/-- On two nonempty fibers with at most thirteen points each, a twin cross
rectangle forces any strategy to act on all paired colors by a single
point permutation. Both the one-color and the two-rectangle cases apply. -/
theorem named_of_twins (p : PerfectStrategy G H K) {l r : Nat}
    (S : Named (Relations.color (closure G)) a b l r) (T : Named (targetName p) a b l r)
    (a₀ : Fin a) (b₀ : Fin b) (ha : a ≤ 13) (hb : b ≤ 13)
    (twins : SplitRectangle.Twins (fun i j => Relations.color (closure G) (S.e (.inl i)) (S.e (.inr j))) ∨
      SplitRectangle.Twins (fun i j => targetName p (T.e (.inl i)) (T.e (.inr j)))) :
    ∃ f : Equiv.Perm (Fin n), ∀ x y, Relations.color (closure G) x y = targetName p (f x) (f y) := by
  let c := fun i j => Relations.color (closure G) (S.e i) (S.e j)
  let d := fun i j => targetName p (T.e i) (T.e j)
  have rect {i j x y} (eq : c i j = c x y) : (i.isLeft,j.isLeft) = (x.isLeft,y.isLeft) := by
    obtain ⟨src,dst⟩ := Relations.end_colors (closure G) eq
    exact Prod.ext (side_eq S src) (side_eq S dst)
  have rectT {i j x y} (eq : d i j = d x y) : (i.isLeft,j.isLeft) = (x.isLeft,y.isLeft) := by
    obtain ⟨src,dst⟩ := Relations.end_colors (closure H) ((target_same p _ _ _ _).mp eq)
    exact Prod.ext (side_eq T ((target_same p _ _ _ _).mpr src)) (side_eq T ((target_same p _ _ _ _).mpr dst))
  have prod : SplitRectangle.Products c d := fun h u v =>
    (count_relabel _ S.e u v _ _).trans ((common_products p u v h).trans (count_relabel _ T.e u v _ _).symm)
  obtain ⟨t,_,ht⟩ := SmallShore.realize_at p (Nat.zero_lt_of_lt b₀.isLt) hb
    (fun j => S.e (.inr j)) (fun j => T.e (.inr j)) r
    (S.e.injective.comp Sum.inr_injective) (T.e.injective.comp Sum.inr_injective) S.right T.right b₀ b₀
  obtain ⟨e,he⟩ := SplitRectangle.realize_either c d a₀ b₀ rect rectT (Relations.transpose _)
    (fun eq => (target_same p _ _ _ _).mpr (Relations.transpose _ ((target_same p _ _ _ _).mp eq)))
    (common_transpose p) prod twins (fun u x => SmallShore.realize_at p (Nat.zero_lt_of_lt a₀.isLt) ha
      (fun i => S.e (.inl i)) (fun i => T.e (.inl i)) l
      (S.e.injective.comp Sum.inl_injective) (T.e.injective.comp Sum.inl_injective) S.left T.left u x) t ht
  refine ⟨S.e.symm.trans (e.trans T.e),?_⟩
  intro x y
  obtain ⟨i,rfl⟩ := S.e.surjective x
  obtain ⟨j,rfl⟩ := S.e.surjective y
  simpa only [Equiv.trans_apply,Equiv.symm_apply_apply] using he i j

theorem graph_of_named (p : PerfectStrategy G H K) (f : Equiv.Perm (Fin n))
    (preserve : ∀ i j, Relations.color (closure G) i j = targetName p (f i) (f j)) : Isomorphic G H :=
  ⟨⟨f,f.symm,f.symm_apply_apply,f.apply_symm_apply,fun i j => common_edge p (preserve i j)⟩⟩

end QGI.Coherent.TwoShore
