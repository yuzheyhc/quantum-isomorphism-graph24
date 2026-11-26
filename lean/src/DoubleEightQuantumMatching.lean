import CoherentDoubleEight
import StrategyColorLaws
import DoubleEightMatchingShore

noncomputable section
open scoped BigOperators

namespace QGI.Coherent.DoubleEightGraphs
open QGI.DoubleEight
open QGI.DoubleEight.ShoreCensus (V side)
open MatchingExtension StrategyColors StrategyColorLaws
open Relations (color)

private def Sides (C : CoherentAlgebra 16) (e : X ≃ Fin 16) : Prop :=
  ∀ u v, side u = side v ↔ color C (e u) (e u) = color C (e v) (e v)

private theorem coordinates_at (H : Graph 16) (sizes : ∀ i, (fiber H i).card = 8) (a : Fin 16) :
    ∃ w : X ≃ Fin 16, Sides (closure H) w ∧ ∃ k : V, w (.inl k) = a := by
  obtain ⟨w,hs⟩ := two_fibers H sizes
  obtain ⟨u,hu⟩ := w.surjective a
  cases u with
  | inl k => exact ⟨w,hs,k,hu⟩
  | inr k =>
    let swap := Equiv.sumComm V V
    have ds (x : X) : side (swap x) = !side x := by cases x <;> rfl
    refine ⟨swap.trans w,fun i j => ?_,k,hu⟩
    apply Iff.trans _ (hs (swap i) (swap j))
    rw [ds,ds]; cases side i <;> cases side j <;> decide

private theorem rectangle_coords (C : CoherentAlgebra 16) (e : X ≃ Fin 16) (hs : Sides C e) :
    Rectangle (fun u w => color C (e u) (e w)) :=
  fun _ _ _ _ eq => Prod.ext ((hs _ _).mpr (Relations.end_colors C eq).1)
    ((hs _ _).mpr (Relations.end_colors C eq).2)

private theorem left_diag (C : CoherentAlgebra 16) (e : X ≃ Fin 16) (hs : Sides C e) :
    LeftDiagonal (fun i j => color C (e i) (e j)) (color C (e (.inl 0)) (e (.inl 0))) := by
  intro x y
  constructor
  · intro h
    have eq := e.injective (Relations.diagonal C h)
    subst y
    cases x with
    | inl i => exact ⟨i,rfl,rfl⟩
    | inr i => exact False.elim (by have z := (hs _ _).mpr h; cases z)
  · rintro ⟨i,rfl,rfl⟩
    exact (hs _ _).mp rfl

/-- A cross-fiber matching in the source graph forces a point isomorphism
for an actual perfect graph strategy. Both eight-point fibers of the
target are identified from their diagonal coherent colors. -/
theorem matching_iso {G H : Graph 16} {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (sizesH : ∀ i, (fiber H i).card = 8)
    (eG : X ≃ Fin 16) (colorSides : ∀ u z, side u = side z ↔ eG u ∈ fiber G (eG z))
    (v : Nat) (sigma : Equiv.Perm V)
    (hit : ∀ i j, color (closure G) (eG (.inl i)) (eG (.inr j)) = v ↔ sigma i = j) :
    Isomorphic G H := by
  let m : Coloring := fun x y => color (closure G) (eG x) (eG y)
  let d := m (.inl 0) (.inl 0)
  have leftG : Sides (closure G) eG := fun u z => (colorSides u z).trans
    (mem_fiber.trans (Relations.same _ _ _ _ _).symm)
  obtain ⟨a,b,supp⟩ := exists_target p (eG (.inl 0)) (eG (.inl 0))
  have diagonal := entry_eq p (Intertwiner.initial_diagonal p) supp
  have samePoint : a = b := by by_contra ne; simp [Matrix.one_apply,ne] at diagonal
  subst b
  obtain ⟨eH,leftH,k,hk⟩ := coordinates_at H sizesH a
  let n : Coloring := fun i j => targetName p (eH i) (eH j)
  let rawH : Coloring := fun i j => color (closure H) (eH i) (eH j)
  have sameH (i j x y : X) : n i j = n x y ↔ rawH i j = rawH x y := target_same p _ _ _ _
  have dd : n (.inl 0) (.inl 0) = d := by
    have base : d = targetName p a a := (associated p).mpr (maps_support p supp)
    rw [base,←hk]
    exact (sameH _ _ _ _).mpr ((leftH _ _).mp rfl)
  have diagN : LeftDiagonal n d := by
    intro x y
    rw [←dd,sameH]
    exact left_diag _ eH leftH _ _
  have rectM : Rectangle m := rectangle_coords _ _ leftG
  have rectN : Rectangle n := fun i j u w eq =>
    rectangle_coords _ _ leftH i j u w ((sameH _ _ _ _).mp eq)
  have hm := left_homogeneous (closure G) eG leftG
  have hn : ShoreCensus.Homogeneous (leftTable n) :=
    homogeneous_rename (fun i j u w => (sameH (.inl i) (.inl j) (.inl u) (.inl w)).symm)
      (left_homogeneous (closure H) eH leftH)
  have common : CommonProducts m n := by
    intro c b i j x y eq
    exact (count_relabel _ eG c b i j).trans ((common_products p c b eq).trans
      (count_relabel _ eH c b x y).symm)
  have forth (i j : X) : ∃ x y, m i j = n x y := by
    obtain ⟨a,b,h⟩ := exists_target p (eG i) (eG j)
    obtain ⟨u,rfl⟩ := eH.surjective a
    obtain ⟨w,rfl⟩ := eH.surjective b
    exact ⟨u,w,(associated p).mpr (maps_support p h)⟩
  have back (x y : X) : ∃ i j, n x y = m i j := by
    obtain ⟨a,b,h⟩ := exists_source p (eH x) (eH y)
    obtain ⟨u,rfl⟩ := eG.surjective a
    obtain ⟨w,rfl⟩ := eG.surjective b
    exact ⟨u,w,((associated p).mpr (maps_support p h)).symm⟩
  obtain ⟨s,hs⟩ := left_realized (left_diag _ eG leftG) diagN rectM rectN hm hn common forth back
  have hmatch : Matches m v sigma := matches_of_rectangle rectM hit
  have tr : CommonTranspose m n := fun _ _ _ _ eq => common_transpose p eq
  obtain ⟨q,hq⟩ := matching_transfers hmatch hs (fun _ _ _ _ eq => Relations.transpose _ eq) tr common
  let F := Equiv.sumCongr s (sigma.symm.trans (s.trans q))
  have preserve (i j : X) : m i j = n (F i) (F j) := extend hmatch hq hs tr common i j
  let f := eG.symm.trans (F.trans eH)
  refine ⟨⟨f,f.symm,f.symm_apply_apply,f.apply_symm_apply,?_⟩⟩
  intro i j
  obtain ⟨i,rfl⟩ := eG.surjective i
  obtain ⟨j,rfl⟩ := eG.surjective j
  simpa only [f, Equiv.trans_apply, Equiv.symm_apply_apply] using common_edge p (preserve i j)

private theorem frame_size {G : Graph 16} (e : X ≃ Fin 16)
    (sides : ∀ u z, side u = side z ↔ e u ∈ fiber G (e z)) (a : Fin 16) :
    (fiber G a).card = 8 := by
  classical
  obtain ⟨w,rfl⟩ := e.surjective a
  let marked := fun i : Fin 16 => if i ∈ fiber G (e w) then (1 : Nat) else 0
  have card : (fiber G (e w)).card = ∑ i, marked i := by simp [marked]
  have pull (x : X) : marked (e x) = if side x = side w then 1 else 0 := by
    simp only [marked, sides]
  rw [card,←Equiv.sum_comp e marked]
  simp_rw [pull]
  cases w <;> rw [Fintype.sum_sum_type] <;> simp [side]

/-- If the source has two eight-point coherent fibers joined by a matching
relation, a quantum-commuting isomorphism to any graph is classical. -/
theorem isomorphic_of_matching {G H : Graph 16} (qc : QuantumIso G H)
    (e : X ≃ Fin 16) (sides : ∀ u z, side u = side z ↔ e u ∈ fiber G (e z))
    (v : Nat) (sigma : Equiv.Perm V)
    (hit : ∀ i j, color (closure G) (e (.inl i)) (e (.inr j)) = v ↔ sigma i = j) :
    Isomorphic G H := by
  obtain ⟨K,g,ip,_,⟨p⟩⟩ := qc
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  apply matching_iso p _ e sides v sigma hit
  intro a
  obtain ⟨i,h⟩ := fiber_size p a
  exact h.symm.trans (frame_size e sides i)
end QGI.Coherent.DoubleEightGraphs