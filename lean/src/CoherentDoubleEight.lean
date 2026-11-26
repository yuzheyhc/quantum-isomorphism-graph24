import CoherentFiberRigidity
import CoherentRelations
import DoubleEightCensus

noncomputable section

namespace QGI.Coherent.DoubleEightGraphs

open QGI.DoubleEight QGI.DoubleEight.ShoreCensus Relations
open scoped BigOperators

theorem two_fibers (G : Graph 16) (sizes : ∀ i, (fiber G i).card = 8) :
    ∃ e : V ⊕ V ≃ Fin 16, ∀ u v, side u = side v ↔
      color (closure G) (e u) (e u) = color (closure G) (e v) (e v) := by
  classical
  let s := fiber G 0
  have mem (i j : Fin 16) : i ∈ fiber G j ↔ color (closure G) i i = color (closure G) j j :=
    mem_fiber.trans (same _ _ _ _ _).symm
  have leftcard : Fintype.card {x // x ∈ s} = 8 := (Fintype.card_coe s).trans (sizes 0)
  have cc : sᶜ.card = 8 := by simp [Finset.card_compl,s,sizes]
  have rightcard : Fintype.card {x : Fin 16 // x ∉ s} = 8 := by
    simpa using (Fintype.card_subtype_compl (fun x => x ∈ s))
      |>.trans (show Fintype.card (Fin 16) - Fintype.card {x // x ∈ s} = 8 by rw [leftcard]; decide)
  let p := Fintype.equivOfCardEq (show Fintype.card V = Fintype.card {x // x ∈ s} by simp [leftcard])
  let q := Fintype.equivOfCardEq (show Fintype.card V = Fintype.card {x : Fin 16 // x ∉ s} by simp [rightcard])
  let e := (Equiv.sumCongr p q).trans (Equiv.sumCompl (fun x => x ∈ s))
  have outside {a : Fin 16} (ha : a ∉ s) : fiber G a = sᶜ := by
    apply Finset.eq_of_subset_of_card_le _ (by rw [sizes,cc])
    intro z hz
    apply Finset.mem_compl.mpr
    exact fun h => ha ((mem a 0).mpr (((mem z a).mp hz).symm.trans ((mem z 0).mp h)))
  have li (i : V) : color (closure G) (p i).val (p i).val = color (closure G) 0 0 :=
    (mem _ _).mp (p i).property
  have ri (j : V) : color (closure G) (q j).val (q j).val ≠ color (closure G) 0 0 :=
    fun h => (q j).property ((mem _ _).mpr h)
  refine ⟨e,?_⟩
  rintro (i|i) (j|j)
  · exact iff_of_true rfl ((li i).trans (li j).symm)
  · exact iff_of_false (by simp [side]) (fun h => ri j (h.symm.trans (li i)))
  · exact iff_of_false (by simp [side]) (fun h => ri i (h.trans (li j)))
  · apply iff_of_true rfl
    apply (mem _ _).mp
    change (q i).val ∈ fiber G (q j).val
    rw [outside (q j).property]
    exact Finset.mem_compl.mpr (q i).property

private theorem pull_products {X Y A : Type} [Fintype X] [Fintype Y] [DecidableEq A]
    (m : X → X → A) (e : Y ≃ X) (h : FixedInterface.HasIntersectionNumbers m) :
    FixedInterface.HasIntersectionNumbers (fun i j => m (e i) (e j)) := by
  intro u v i j x y eq
  have shift (a b : Y) := Equiv.sum_comp e (fun z => (if m (e a) z = u ∧ m z (e b) = v then 1 else 0 : Nat))
  exact (shift i j).trans ((h u v _ _ _ _ eq).trans (shift x y).symm)

theorem left_homogeneous (C : CoherentAlgebra 16) (e : V ⊕ V ≃ Fin 16)
    (sides : ∀ u v, side u = side v ↔ color C (e u) (e u) = color C (e v) (e v)) :
    Homogeneous (fun i j => color C (e (.inl i)) (e (.inl j))) := by
  let m := fun u v => color C (e u) (e v)
  have law := pull_products _ e (Relations.products C)
  refine ⟨fun i j => ?_, fun _ _ _ _ eq => Relations.transpose C eq,?_⟩
  · constructor
    · intro eq; exact Sum.inl.inj (e.injective (Relations.diagonal C eq))
    · rintro rfl; exact (sides _ _).mp rfl
  intro i j x y eq a b
  by_cases occurs : ∃ u v : V, m (.inl u) (.inl v) = a
  · obtain ⟨u,v,rfl⟩ := occurs
    have forbid (i k : V) : m (.inl i) (.inr k) ≠ m (.inl u) (.inl v) := by
      intro h
      have nonsense := (sides (.inr k) (.inl v)).mpr (Relations.end_colors C h).2
      cases nonsense
    have h := law (m (.inl u) (.inl v)) b (.inl i) (.inl j) (.inl x) (.inl y) eq
    change (∑ z, if m (.inl i) z = _ ∧ m z (.inl j) = b then 1 else 0 : Nat) =
      (∑ z, if m (.inl x) z = _ ∧ m z (.inl y) = b then 1 else 0 : Nat) at h
    simp only [Fintype.sum_sum_type] at h
    simp only [forbid,false_and,if_false,Finset.sum_const_zero,add_zero] at h
    exact h
  · push_neg at occurs
    change intersection (fun i j => m (.inl i) (.inl j)) a b i j = _
    simpa [intersection,m] using (by simp [intersection,occurs] :
      intersection (fun i j => m (.inl i) (.inl j)) a b i j =
      intersection (fun i j => m (.inl i) (.inl j)) a b x y)
def HasCrossMatching (G : Graph 16) : Prop :=
  ∃ (e : V ⊕ V ≃ Fin 16) (v : Nat) (p : Equiv.Perm V),
    (∀ u w, side u = side w ↔ e u ∈ fiber G (e w)) ∧
    ∀ i j, color (closure G) (e (.inl i)) (e (.inr j)) = v ↔ p i = j

/-- The chosen catalog row realizes every basic relation of the graph's
closure. Its vertices and color names may both be relabeled. -/
theorem matching_or_partition (G : Graph 16) (sizes : ∀ i, (fiber G i).card = 8) :
    HasCrossMatching G ∨
    ∃ (t : Nat) (row : Array Nat) (f : Equiv.Perm (Fin 16)), Layers.matrices[t]? = some row ∧
      ∀ i j x y, color (closure G) i j = color (closure G) x y ↔
        Placements.color row (f i) (f j) = Placements.color row (f x) (f y) := by
  classical
  obtain ⟨e,sides⟩ := two_fibers G sizes
  let C := closure G
  let m := fun u v => color C (e u) (e v)
  have rectangle (u v x y) (eq : m u v = m x y) :
      (side u,side v) = (side x,side y) :=
    Prod.ext ((sides _ _).mpr (end_colors C eq).1) ((sides _ _).mpr (end_colors C eq).2)
  let swap := Equiv.sumComm V V
  have ds (i) : side (swap i) = !side i := by cases i <;> rfl
  have hs (u v) : side u = side v ↔ color C (e (swap u)) (e (swap u)) = color C (e (swap v)) (e (swap v)) := by
    apply Iff.trans _ (sides (swap u) (swap v))
    rw [ds,ds]; cases side u <;> cases side v <;> decide
  have hr := left_homogeneous C (swap.trans e) hs
  rcases Census.matching_or_catalog m (left_homogeneous C e sides) hr rectangle
    (fun _ _ _ _ eq => Relations.transpose C eq) (pull_products _ e (Relations.products C)) with
      ⟨v,p,h⟩ | ⟨t,row,mem,g,hg⟩
  · exact Or.inl ⟨e,v,p,fun u w => (sides u w).trans ((same C _ _ _ _).trans mem_fiber.symm),h⟩
  · let f := e.symm.trans g
    refine Or.inr ⟨t,row,f,mem,fun i j x y => ?_⟩
    simpa only [m,f,Equiv.trans_apply,Equiv.apply_symm_apply] using hg (e.symm i) (e.symm j) (e.symm x) (e.symm y)

/-- A graph with two 8-point coherent fibers either has a matching basis
relation between them, or its edges are the union of colors of an actual
catalog matrix after a single permutation of its sixteen vertices. -/
theorem matching_or_union (G : Graph 16) (sizes : ∀ i, (fiber G i).card = 8) :
    (∃ (e : V ⊕ V ≃ Fin 16) (v : Nat) (p : Equiv.Perm V),
      (∀ u w, side u = side w ↔ e u ∈ fiber G (e w)) ∧
      ∀ i j, color (closure G) (e (.inl i)) (e (.inr j)) = v ↔ p i = j) ∨
    (∃ (t : Nat) (row : Array Nat) (f : Equiv.Perm (Fin 16)) (edges : Nat → Bool),
      Layers.matrices[t]? = some row ∧ ∀ i j, G.edge i j = edges (Placements.color row (f i) (f j))) := by
  classical
  rcases matching_or_partition G sizes with hit | ⟨t,row,f,mem,hf⟩
  · exact Or.inl hit
  · let C := closure G
    let d := fun i j => Placements.color row (f i) (f j)
    have sameColor (i j x y : Fin 16) : color C i j = color C x y ↔ d i j = d x y := hf i j x y
    have edge (i j x y) (eq : d i j = d x y) : G.edge i j = G.edge x y := by
      have h := (same C _ _ _ _).mp ((sameColor _ _ _ _).mpr eq) _ (adjacency_mem G)
      cases hi : G.edge i j <;> cases hx : G.edge x y <;> first | rfl | simp [Intertwiner.adjacency,hi,hx] at h
    let active := fun col => decide (∃ x y, d x y = col ∧ G.edge x y = true)
    refine Or.inr ⟨t,row,f,active,mem,fun i j => ?_⟩
    change G.edge i j = decide (∃ x y, d x y = d i j ∧ G.edge x y = true)
    by_cases yes : G.edge i j = true
    · simp [yes, show ∃ x y, d x y = d i j ∧ G.edge x y = true from ⟨i,j,rfl,yes⟩]
    · have empty : ¬∃ x y, d x y = d i j ∧ G.edge x y = true := by
        rintro ⟨x,y,eq,ax⟩; exact yes ((edge _ _ _ _ eq).symm.trans ax)
      simp [empty,yes, Bool.eq_false_iff.mpr yes]

end QGI.Coherent.DoubleEightGraphs