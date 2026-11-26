import DoubleEightShoreCensus
import GraphTypes
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace QGI.DoubleEight.MatchingExtension
open ShoreCensus (V side)
open Finset
open scoped BigOperators

abbrev X := V ⊕ V
abbrev Coloring := X → X → Nat

/-- Association of the two color tables after putting their palettes in common
names. Two endpoints with the same color have the same intersection numbers. -/
def CommonProducts (m n : Coloring) : Prop :=
  ∀ a b i j x y, m i j = n x y →
    (∑ k, if m i k = a ∧ m k j = b then 1 else 0 : Nat) =
    (∑ k, if n x k = a ∧ n k y = b then 1 else 0 : Nat)

def CommonTranspose (m n : Coloring) : Prop :=
  ∀ i j x y, m i j = n x y → m j i = n y x

def Matches (m : Coloring) (v : Nat) (p : Equiv.Perm V) : Prop :=
  ∀ i w, m (.inl i) w = v ↔ w = .inr (p i)

/-- The matching-color alternative in the census, together with the usual
rectangle law, yields uniqueness even when the second endpoint is untyped. -/
theorem matches_of_rectangle {m : Coloring} {v : Nat} {p : Equiv.Perm V}
    (rect : ∀ i j x y, m i j = m x y → (side i,side j) = (side x,side y))
    (h : ∀ i j, m (.inl i) (.inr j) = v ↔ p i = j) : Matches m v p := by
  intro i w
  cases w with
  | inl j =>
    constructor
    · intro eq
      have e := rect _ _ _ _ (eq.trans ((h i (p i)).mpr rfl).symm)
      simp [side] at e
    · intro e; cases e
  | inr j => simpa [eq_comm] using h i j

private theorem common_symm {m n : Coloring} (h : CommonProducts m n) : CommonProducts n m :=
  fun a b i j x y e => (h a b x y i j e.symm).symm

private theorem middle {m n : Coloring} (h : CommonProducts m n)
    {i j x y : X} (eq : m i j = n x y) (k : X) :
    ∃ w, n x w = m i k ∧ n w y = m k j := by
  have counts := h (m i k) (m k j) i j x y eq
  have cards : (univ.filter (fun z => m i z = m i k ∧ m z j = m k j)).card =
      (univ.filter (fun z => n x z = m i k ∧ n z y = m k j)).card := by
    simpa only [Finset.sum_boole] using counts
  have positive : 0 < (univ.filter (fun z => m i z = m i k ∧ m z j = m k j)).card :=
    card_pos.mpr ⟨k,mem_filter.mpr ⟨mem_univ _,rfl,rfl⟩⟩
  obtain ⟨w,hw⟩ := card_pos.mp (cards ▸ positive)
  exact ⟨w,(mem_filter.mp hw).2⟩

/-- A matching in the source forces a matching of the same common color in
the target. Two source points sharing a target neighbor would give a
two-step witness contradicting injectivity of the source matching. -/
theorem matching_transfers {m n : Coloring} {v : Nat} {p e : Equiv.Perm V}
    (hm : Matches m v p) (left : ∀ i j, m (.inl i) (.inl j) = n (.inl (e i)) (.inl (e j)))
    (rev : ∀ i j x y, m i j = m x y → m j i = m y x)
    (tr : CommonTranspose m n) (products : CommonProducts m n) : ∃ q, Matches n v q := by
  classical
  have edge (i : V) : m (.inl i) (.inr (p i)) = v := (hm i _).mpr rfl
  have right (i : V) (w : X) (h : n (.inl (e i)) w = v) : ∃ z : V, w = .inr z := by
    cases w with
    | inr z => exact ⟨_,rfl⟩
    | inl u =>
      have falseEq := (hm i (.inl (e.symm u))).mp ((left i (e.symm u)).trans (by simpa using h))
      cases falseEq
  have present (i : V) : ∃ z : V, n (.inl (e i)) (.inr z) = v := by
    obtain ⟨w,hw,_⟩ := middle products (left i i) (.inr (p i))
    obtain ⟨z,rfl⟩ := right i w (hw.trans (edge i))
    exact ⟨z,hw.trans (edge i)⟩
  let f := fun i : V => (present i).choose
  have hf (i : V) : n (.inl (e i)) (.inr (f i)) = v := (present i).choose_spec
  have separate (i j : V) (w : X) (h₁ : n (.inl (e i)) w = v) (h₂ : n (.inl (e j)) w = v) : i = j := by
    have back := tr _ _ _ _ ((edge j).trans h₂.symm)
    obtain ⟨z,hz,hz'⟩ := middle (common_symm products) (left i j).symm w
    have z₁ := (hm i z).mp (hz.trans h₁)
    have z₂ := (hm j z).mp ((rev _ _ _ _ (hz'.trans back.symm)).trans (edge j))
    exact p.injective (Sum.inr.inj (z₁.symm.trans z₂))
  have inj : Function.Injective f := fun i j eq => separate i j (.inr (f i)) (hf i) (eq ▸ hf j)
  let bij := Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj)
  refine ⟨e.symm.trans bij, ?_⟩
  intro x w
  obtain ⟨i,rfl⟩ := e.surjective x
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  constructor
  · intro h
    obtain ⟨z,rfl⟩ := right i w h
    obtain ⟨j,hj⟩ := bij.surjective z
    have equal : i = j := separate i j (.inr z) h (hj ▸ hf j)
    rw [equal,hj]
  · rintro rfl
    exact hf i

/-- After fixing a point realization on the left, the right-shore map is
forced by the matching. Products and transpose transfer every cross and
right-shore color along this explicit full point bijection. -/
theorem extend {m n : Coloring} {v : Nat} {p q e : Equiv.Perm V}
    (hm : Matches m v p) (hn : Matches n v q)
    (left : ∀ i j, m (.inl i) (.inl j) = n (.inl (e i)) (.inl (e j)))
    (tr : CommonTranspose m n) (products : CommonProducts m n) :
    let f := Equiv.sumCongr e (p.symm.trans (e.trans q))
    ∀ i j, m i j = n (f i) (f j) := by
  have edge (i : V) : m (.inl i) (.inr (p i)) = v := (hm i _).mpr rfl
  have rl (i j : V) : m (.inr (p i)) (.inl j) = n (.inr (q (e i))) (.inl (e j)) := by
    obtain ⟨w,hw,hw'⟩ := middle products (left i j) (.inr (p i))
    rw [(hn (e i) w).mp (hw.trans (edge i))] at hw'
    exact hw'.symm
  have lr (i j : V) := tr _ _ _ _ (rl j i)
  have rr (i j : V) : m (.inr (p i)) (.inr (p j)) = n (.inr (q (e i))) (.inr (q (e j))) := by
    obtain ⟨w,hw,hw'⟩ := middle products (lr i j) (.inr (p i))
    rw [(hn (e i) w).mp (hw.trans (edge i))] at hw'
    exact hw'.symm
  dsimp only
  rintro (i|i) (j|j)
  · exact left i j
  · simpa using lr i (p.symm j)
  · simpa using rl (p.symm i) j
  · simpa using rr (p.symm i) (p.symm j)

/-- Graph consequence with arbitrary identifications of the two shores with
Fin 16 and a shared interpretation of color names as edge/nonedge. -/
theorem graphs_isomorphic {m n : Coloring} {v : Nat} {p e : Equiv.Perm V}
    (hm : Matches m v p) (left : ∀ i j, m (.inl i) (.inl j) = n (.inl (e i)) (.inl (e j)))
    (rev : ∀ i j x y, m i j = m x y → m j i = m y x)
    (tr : CommonTranspose m n) (products : CommonProducts m n)
    (G H : QGI.Graph 16) (u w : X ≃ Fin 16) (isEdge : Nat → Bool)
    (g : ∀ i j, G.edge (u i) (u j) = isEdge (m i j))
    (h : ∀ i j, H.edge (w i) (w j) = isEdge (n i j)) : QGI.Isomorphic G H := by
  obtain ⟨q,hq⟩ := matching_transfers hm left rev tr products
  let F := Equiv.sumCongr e (p.symm.trans (e.trans q))
  let f := u.symm.trans (F.trans w)
  refine ⟨⟨f,f.symm,f.symm_apply_apply,f.apply_symm_apply,?_⟩⟩
  rintro i j
  obtain ⟨i,rfl⟩ := u.surjective i
  obtain ⟨j,rfl⟩ := u.surjective j
  simpa only [f,Equiv.trans_apply,Equiv.symm_apply_apply,g,h] using
    congrArg isEdge (extend hm hq left tr products i j)

end QGI.DoubleEight.MatchingExtension
