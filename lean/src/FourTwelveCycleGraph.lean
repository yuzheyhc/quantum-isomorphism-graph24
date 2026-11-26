import FourTwelveCycle
import SixTenCoordinates

noncomputable section
namespace QGI.Coherent.FourTwelveCycleGraph
open StrategyColorLaws FourTwelveCycle

abbrev V := Fin 16
abbrev L := Fin 4
abbrev R := Fin 12
abbrev C := V → V → Nat

structure Frame (c : C) where
  points : L ⊕ R ≃ V
  l : Nat
  r : Nat
  ne : l ≠ r
  leftDiag : ∀ i, c (points (.inl i)) (points (.inl i)) = l
  rightDiag : ∀ j, c (points (.inr j)) (points (.inr j)) = r

namespace Frame
variable {c : C} (f : Frame c)
def left : L ↪ V := ⟨fun i => f.points (.inl i),fun _ _ h => Sum.inl.inj (f.points.injective h)⟩
def right : R ↪ V := ⟨fun i => f.points (.inr i),fun _ _ h => Sum.inr.inj (f.points.injective h)⟩

theorem left_iff (z : V) : (∃ i, f.left i = z) ↔ c z z = f.l := by
  obtain ⟨i,rfl⟩ := f.points.surjective z
  cases i with
  | inl i => exact iff_of_true ⟨i,rfl⟩ (f.leftDiag _)
  | inr j =>
    exact iff_of_false (by rintro ⟨_,h⟩; cases f.points.injective h)
      (fun h => f.ne (h.symm.trans (f.rightDiag _)))

theorem right_iff (z : V) : (∃ i, f.right i = z) ↔ c z z = f.r := by
  obtain ⟨i,rfl⟩ := f.points.surjective z
  cases i with
  | inr j => exact iff_of_true ⟨j,rfl⟩ (f.rightDiag _)
  | inl i =>
    exact iff_of_false (by rintro ⟨_,h⟩; cases f.points.injective h)
      (fun h => f.ne ((f.leftDiag _).symm.trans h))
end Frame

/-- A source-only description of the repeated four-cycle branch. The
cross adjacency can be the indicated relation or its complement. -/
structure Presentation (G : Graph 16) where
  f : Frame (Relations.color (closure G))
  name : Nat
  column : R → Edge
  shape : ∀ y, ∃ i, column y = cycle i
  full : ∀ i, ∃ y, column y = cycle i
  cells : ∀ y, neighbors (Relations.color (closure G)) name (f.right y) = (edge (column y)).map f.left
  select : Bool → Bool
  adjacency : ∀ y i, G.edge (f.right y) (f.left i) =
    select (decide (Relations.color (closure G) (f.right y) (f.left i) = name))

private theorem edgeSize : ∀ e : Edge, (edge e).card = 2 := by native_decide
private theorem allEdges : ∀ s : Finset L, s.card = 2 → ∃ e, edge e = s := by native_decide

private def induced (G : Graph 16) (f : L ↪ V) : Graph 4 :=
  ⟨fun i j => G.edge (f i) (f j),fun i j => G.symm (f i) (f j),fun i => G.loopless (f i)⟩

variable {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

/-- Any named source fiber decomposition transports to the target. A
bijection of intermediate vertices for one corresponding pair transports
all diagonal names simultaneously. -/
theorem targetFrame (f : Frame (Relations.color (closure G))) :
    ∃ g : Frame (targetName p), g.l = f.l ∧ g.r = f.r := by
  obtain ⟨x,y,hit⟩ := StrategyColors.exists_target p 0 0
  have eq := (associated p).mpr (StrategyColors.maps_support p hit)
  obtain ⟨e,he⟩ := (SixTenCoordinates.commonLaws p).middle eq
  have diags (z : V) : Relations.color (closure G) z z = targetName p (e z) (e z) :=
    (SmallShore.endpoints p (he z).1).2
  exact ⟨⟨f.points.trans e,f.l,f.r,f.ne,fun i => (diags _).symm.trans (f.leftDiag i),
      fun j => (diags _).symm.trans (f.rightDiag j)⟩,rfl,rfl⟩

/-- A named realization of the right fiber transports arbitrary two-element
neighborhoods. Their whole intersection matrix is preserved. -/
theorem transport_columns {cName : Nat} (f : Frame (Relations.color (closure G))) (g : Frame (targetName p))
    (Lname : g.l = f.l) (r : Equiv.Perm R)
    (names : ∀ i j, Relations.color (closure G) (f.right i) (f.right j) =
      targetName p (g.right (r i)) (g.right (r j)))
    (a : R → Edge) (cells : ∀ j, neighbors (Relations.color (closure G)) cName (f.right j) =
      (edge (a j)).map f.left) :
    ∃ b : R → Edge, (∀ j, neighbors (targetName p) cName (g.right (r j)) = (edge (b j)).map g.left) ∧
      ∀ i j, overlap (a i) (a j) = overlap (b i) (b j) := by
  classical
  let c := Relations.color (closure G)
  let d := targetName p
  let src := fun j => neighbors c cName (f.right j)
  let dst := fun j => neighbors d cName (g.right (r j))
  have sc (j) : src j = (edge (a j)).map f.left := cells j
  have counts (i j : R) := shared_counts p cName (names i j)
  have describe (j : R) : ∃ t : Edge, dst j = (edge t).map g.left := by
    obtain ⟨e,he⟩ := (SixTenCoordinates.commonLaws p).middle (names j j)
    have contained (z : V) (hz : z ∈ dst j) : ∃ i, g.left i = z := by
      obtain ⟨k,rfl⟩ := e.surjective z
      have incl : k ∈ src j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (he k).1.trans (Finset.mem_filter.mp hz).2⟩
      obtain ⟨i,_,hi⟩ := Finset.mem_map.mp ((sc j) ▸ incl)
      apply (g.left_iff _).mpr
      exact ((SmallShore.endpoints p (he k).1).2).symm.trans
        ((f.left_iff _).mp ⟨i,hi⟩ |>.trans Lname.symm)
    let s := Finset.univ.filter (fun i => g.left i ∈ dst j)
    have es : s.map g.left = dst j := by
      ext z
      constructor
      · rintro hz
        obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hz
        exact (Finset.mem_filter.mp hi).2
      · intro hz
        obtain ⟨i,rfl⟩ := contained z hz
        exact Finset.mem_map.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩,rfl⟩
    have cs : (src j).card = (dst j).card := by
      simpa only [Finset.inter_self] using (counts j j).1
    rw [sc,←es,Finset.card_map,Finset.card_map,edgeSize] at cs
    obtain ⟨t,ht⟩ := allEdges s cs.symm
    exact ⟨t,ht.symm ▸ es.symm⟩
  choose b hb using describe
  have gram (i j : R) : overlap (a i) (a j) = overlap (b i) (b j) := by
    have h : (src i ∩ src j).card = (dst i ∩ dst j).card := (counts i j).1
    simpa only [sc,hb,←Finset.map_inter,Finset.card_map,overlap] using h
  exact ⟨b,hb,gram⟩

include p in
theorem isomorphic (S : Presentation G) : Isomorphic G H := by
  classical
  let c := Relations.color (closure G)
  let d := targetName p
  let f := S.f
  obtain ⟨g,Lname,Rname⟩ := targetFrame p f
  obtain ⟨r,_,names⟩ := SmallShore.realize_at p (by decide : 0 < 12) (by decide)
    f.right g.right f.r f.right.injective g.right.injective f.right_iff
    (fun z => by rw [←Rname]; exact g.right_iff z) 0 0
  obtain ⟨b,hb,gram⟩ := transport_columns p f g Lname r names S.column S.cells
  let src := fun j => neighbors c S.name (f.right j)
  let dst := fun j => neighbors d S.name (g.right (r j))
  change ∀ j, dst j = (edge (b j)).map g.left at hb
  have sc (j) : src j = (edge (S.column j)).map f.left := S.cells j
  have counts (i j : R) := shared_counts p S.name (names i j)
  let A := induced G f.left
  let B := induced H g.left
  have pulled (i j : R) : moment A.edge (edge (S.column i)) (edge (S.column j)) =
      moment B.edge (edge (b i)) (edge (b j)) := by
    have h : moment G.edge (src i) (src j) = moment H.edge (dst i) (dst j) := (counts i j).2
    simpa only [sc,hb,moment,Finset.sum_map,A,B,induced] using h
  obtain ⟨e,internal,cross⟩ := realize S.column b (Equiv.refl R) A B S.shape S.full gram pulled
  have targetAdj (y : R) (i : L) : H.edge (g.right y) (g.left i) =
      S.select (decide (d (g.right y) (g.left i) = S.name)) := by
    obtain ⟨u,w,hit⟩ := StrategyColors.exists_source p (g.right y) (g.left i)
    have eq := (associated p).mpr (StrategyColors.maps_support p hit)
    obtain ⟨h₁,h₂⟩ := SmallShore.endpoints p eq
    obtain ⟨j,rfl⟩ := (f.right_iff u).mpr (h₁.trans ((g.rightDiag y).trans Rname))
    obtain ⟨k,rfl⟩ := (f.left_iff w).mpr (h₂.trans ((g.leftDiag i).trans Lname))
    rw [←common_edge p eq,S.adjacency]
    exact congrArg (fun t => S.select (decide (t = S.name))) eq
  have crossEdge (j : R) (i : L) : G.edge (f.right j) (f.left i) = H.edge (g.right (r j)) (g.left (e i)) := by
    have l (u : L) : (f.left u ∈ src j) ↔ u ∈ edge (S.column j) := by rw [sc]; simp
    have t (u : L) : (g.left u ∈ dst j) ↔ u ∈ edge (b j) := by rw [hb]; simp
    have inc : i ∈ edge (S.column j) ↔ e i ∈ edge (b j) := by
      rw [←show (edge (S.column j)).map e.toEmbedding = edge (b j) from cross j]
      simp
    have agree := (l i).trans (inc.trans (t _).symm)
    change (f.left i ∈ Finset.univ.filter _) ↔ (g.left (e i) ∈ Finset.univ.filter _) at agree
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at agree
    rw [S.adjacency,targetAdj]
    apply congrArg S.select
    exact Bool.decide_congr agree
  let total := f.points.symm.trans ((Equiv.sumCongr e r).trans g.points)
  refine ⟨total,total.symm,total.symm_apply_apply,total.apply_symm_apply,?_⟩
  intro x y
  obtain ⟨i,rfl⟩ := f.points.surjective x
  obtain ⟨j,rfl⟩ := f.points.surjective y
  simp only [total,Equiv.trans_apply,Equiv.symm_apply_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j => exact internal i j
    | inr j => exact (G.symm _ _).trans ((crossEdge j i).trans (H.symm _ _))
  | inr i =>
    cases j with
    | inl j => exact crossEdge i j
    | inr j => exact common_edge p (names i j)

theorem isomorphic_of_quantum (S : Presentation G) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,g,ip,_,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  exact isomorphic p S

end QGI.Coherent.FourTwelveCycleGraph




