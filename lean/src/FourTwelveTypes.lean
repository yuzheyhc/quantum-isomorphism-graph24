import FourTwelveCycleGraph
import FourTwelveFunctional
import TwoShoreRealization

noncomputable section
namespace QGI.Coherent.FourTwelveTypes
open FourTwelveCycle FourTwelveCycleGraph StrategyColorLaws

/-- Each of the six edges of the four-point set labels two columns. -/
structure Doubled (c : C) (f : Frame c) (v : Nat) where
  column : R → Edge
  cells : ∀ j, neighbors c v (f.right j) = (edge (column j)).map f.left
  twice : ∀ e, (Finset.univ.filter fun j => column j = e).card = 2

def opposite : Edge → Edge := ![5,4,3,2,1,0]

theorem opposite_edge : ∀ e : Edge, edge (opposite e) = (edge e)ᶜ := by native_decide
theorem opposite_invol : ∀ e : Edge, opposite (opposite e) = e := by native_decide
theorem edge_inj : Function.Injective edge := by native_decide
theorem edge_overlap : ∀ e f : Edge, overlap e f = 2 ↔ e=f := by native_decide

private theorem alternatives : ∀ s : Finset Edge, s.Nonempty → (∀ e, e ∈ s ↔ opposite e ∈ s) →
    (∃ e ∈ s, ∀ k ∈ s, k=e ∨ k=opposite e) ∨
    (∃ p : Equiv.Perm L, ∀ k, k ∈ s ↔ ∃ i, edge k = (edge (cycle i)).map p.toEmbedding) ∨
    s = Finset.univ := by native_decide

def degree {m : Nat} (b : Fin m → Edge) (i : L) := (Finset.univ.filter fun j => i ∈ edge (b j)).card
def mult {m : Nat} (b : Fin m → Edge) (e : Edge) := (Finset.univ.filter fun j => b j=e).card

/-- Equal point degrees on a four-point set force opposite pairs to have
equal multiplicity, for every number of columns. -/
theorem opposite_mult {m : Nat} (b : Fin m → Edge) (rows : ∀ i, degree b i = degree b 0) :
    ∀ e, mult b e = mult b (opposite e) := by
  have counts (i : L) : degree b i = ∑ e ∈ Finset.univ.filter (fun e => i ∈ edge e), mult b e := by
    symm
    simpa [degree,mult] using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin m)) (Finset.univ.filter (fun e : Edge => i ∈ edge e)) b
  have h₁ := rows 1
  have h₂ := rows 2
  have h₃ := rows 3
  simp only [counts] at h₁ h₂ h₃
  have sets : ∀ i : L, Finset.univ.filter (fun e => i ∈ edge e) =
      (![({0,1,2} : Finset Edge),{0,3,4},{1,3,5},{2,4,5}] i) := by native_decide
  simp [sets] at h₁ h₂ h₃
  intro e
  fin_cases e <;> change mult b _ = mult b _ <;> dsimp [opposite] <;> omega

/-- The distinct two-point neighborhoods are a matching, a four-cycle,
or all six edges. Only row regularity is needed for this trichotomy. -/
theorem shapes {m : Nat} [NeZero m] (b : Fin m → Edge) (rows : ∀ i, degree b i = degree b 0) :
    (∃ e, ∀ j, b j=e ∨ b j=opposite e) ∨
    (∃ p : Equiv.Perm L,
      (∀ y, ∃ i, edge (b y) = (edge (cycle i)).map p.toEmbedding) ∧
      ∀ i, ∃ y, edge (b y) = (edge (cycle i)).map p.toEmbedding) ∨
    Function.Surjective b := by
  let s := Finset.univ.image b
  have mem (e) : e ∈ s ↔ ∃ j, b j=e := by simp [s]
  have pos (e) : e ∈ s ↔ 0 < mult b e := by simp [s,mult,Finset.card_pos,Finset.Nonempty]
  have op (e) : e ∈ s ↔ opposite e ∈ s := by rw [pos,pos,opposite_mult b rows]
  rcases alternatives s ⟨b 0,(mem _).mpr ⟨0,rfl⟩⟩ op with ⟨e,_,matched⟩|⟨p,cycleCase⟩|full
  · exact Or.inl ⟨e,fun j => matched _ ((mem _).mpr ⟨j,rfl⟩)⟩
  · refine Or.inr (Or.inl ⟨p,fun y => (cycleCase _).mp ((mem _).mpr ⟨y,rfl⟩),?_⟩)
    intro i
    have allPairs : ∀ k : Finset L, k.card = 2 → ∃ t, edge t = k := by native_decide
    have pairSize : ∀ k : Edge, (edge k).card = 2 := by native_decide
    obtain ⟨k,hk⟩ := allPairs ((edge (cycle i)).map p.toEmbedding) (by simp [pairSize])
    obtain ⟨j,hj⟩ := (mem k).mp ((cycleCase k).mpr ⟨i,hk⟩)
    exact ⟨j,hj ▸ hk⟩
  · exact Or.inr (Or.inr (fun e => (mem e).mp (full ▸ Finset.mem_univ _)))

end QGI.Coherent.FourTwelveTypes

namespace QGI.Coherent.FourTwelveTypes
open FourTwelveCycle FourTwelveCycleGraph StrategyColorLaws SixTenCoordinates

private abbrev SFrame := FourTwelveCycleGraph.Frame

/-- Choose coordinates on the two source fibers, from their sizes alone. -/
theorem coordinates {G : Graph 16} (four : ∃ x, (fiber G x).card = 4)
    (twelve : ∃ x, (fiber G x).card = 12) : Nonempty (SFrame (Relations.color (closure G))) := by
  classical
  obtain ⟨x,hx⟩ := four
  obtain ⟨y,hy⟩ := twelve
  let c := Relations.color (closure G)
  let s := fiber G x
  let t := fiber G y
  have dx (z) : z ∈ s ↔ c z z = c x x := FourTwelveFunctional.fiber_eq x z
  have dy (z) : z ∈ t ↔ c z z = c y y := FourTwelveFunctional.fiber_eq y z
  have ne : c x x ≠ c y y := by
    intro same
    have eq : s = t := by ext z; rw [dx,dy,same]
    have := congrArg Finset.card eq
    change (fiber G x).card = (fiber G y).card at this
    omega
  have comp : t = sᶜ := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      exact Finset.mem_compl.mpr (fun hs => ne (((dx z).mp hs).symm.trans ((dy z).mp hz)))
    · simp [Finset.card_compl,s,t,hx,hy]
  let l := Fintype.equivOfCardEq (show Fintype.card L = Fintype.card {z // z ∈ s} by simp [s,hx])
  let r := Fintype.equivOfCardEq (show Fintype.card R = Fintype.card {z : Fin 16 // z ∉ s} by
    rw [Fintype.card_subtype_compl,Fintype.card_coe]; simp [s,hx])
  refine ⟨⟨(Equiv.sumCongr l r).trans (Equiv.sumCompl _), c x x,c y y,ne,?_,?_⟩⟩
  · exact fun i => (dx _).mp (l i).property
  · exact fun j => (dy _).mp (comp ▸ Finset.mem_compl.mpr (r j).property)

def leftShore {c : C} (f : SFrame c) : Shore c f.l L := by
  let fn (i : L) : {z // c z z = f.l} := ⟨f.left i,f.leftDiag i⟩
  exact Equiv.ofBijective fn ⟨fun _ _ h => f.left.injective (congrArg Subtype.val h),
    fun z => by obtain ⟨i,h⟩ := (f.left_iff _).mpr z.property; exact ⟨i,Subtype.ext h⟩⟩

def rightShore {c : C} (f : SFrame c) : Shore c f.r R := by
  let fn (i : R) : {z // c z z = f.r} := ⟨f.right i,f.rightDiag i⟩
  exact Equiv.ofBijective fn ⟨fun _ _ h => f.right.injective (congrArg Subtype.val h),
    fun z => by obtain ⟨i,h⟩ := (f.right_iff _).mpr z.property; exact ⟨i,Subtype.ext h⟩⟩

def crosses {c : C} (f : SFrame c) (j : R) (i : L) := c (f.right j) (f.left i)
def active {c : C} (f : SFrame c) (v : Nat) (j : R) (i : L) := decide (crosses f j i = v)

theorem regular {c : C} (law : Laws c c) (f : SFrame c) (v : Nat) :
    (∀ j, FiberRectangles.degree (active f v j) = FiberRectangles.degree (active f v 0)) ∧
    (∀ i, FiberRectangles.degree (fun j => active f v j i) = FiberRectangles.degree (fun j => active f v j 0)) ∧
    ∀ j k, Block.hist (Block.overlap (active f v)) j k = Block.hist (Block.overlap (active f v)) 0 k := by
  have h : Block (rightShore f) (rightShore f) (leftShore f) (leftShore f) (active f v) (active f v) :=
    fun ⦃_ _ _ _⦄ h => congrArg (fun t => decide (t = v)) h
  exact ⟨fun j => Block.degree_eq law h j 0,fun i => Block.degree_eq law (Block.flip law h) i 0,
    fun j k => Block.hist_eq law (Block.gram law h) j 0 k⟩

theorem twins_graph {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (f : SFrame (Relations.color (closure G)))
    (twins : SplitRectangle.Twins (crosses f)) : Isomorphic G H := by
  obtain ⟨g,hl,hr⟩ := FourTwelveCycleGraph.targetFrame p f
  let a : TwoShore.Named (Relations.color (closure G)) 12 4 f.r f.l :=
    ⟨(Equiv.sumComm _ _).trans f.points,f.right_iff,f.left_iff⟩
  let b : TwoShore.Named (targetName p) 12 4 f.r f.l :=
    ⟨(Equiv.sumComm _ _).trans g.points,fun i => (g.right_iff i).trans (hr ▸ Iff.rfl),
      fun i => (g.left_iff i).trans (hl ▸ Iff.rfl)⟩
  obtain ⟨e,he⟩ := TwoShore.named_of_twins p a b 0 0 (by decide) (by decide) (Or.inl twins)
  exact TwoShore.graph_of_named p e he

end QGI.Coherent.FourTwelveTypes


namespace QGI.Coherent.FourTwelveTypes
open FourTwelveCycle FourTwelveCycleGraph StrategyColorLaws

theorem transfer_twice (a b : R → Edge) (full : Function.Surjective a) (two : ∀ e, mult a e = 2)
    (same : ∀ i j, a i = a j ↔ b i = b j) : ∀ e, mult b e = 2 := by
  choose rep hr using full
  let f := fun e => b (rep e)
  have inj : Function.Injective f := fun i j h =>
    (hr i).symm.trans (((same _ _).mpr h).trans (hr j))
  intro e
  obtain ⟨i,hi⟩ := Finite.injective_iff_surjective.mp inj e
  have eq : Finset.univ.filter (fun j => b j=e) = Finset.univ.filter (fun j => a j=i) := by
    apply Finset.filter_congr
    intro j _
    calc
      b j = e ↔ b j = b (rep i) := by rw [←hi]
      _ ↔ a j = a (rep i) := (same j (rep i)).symm
      _ ↔ a j = i := by rw [hr]
  exact (congrArg Finset.card eq).trans (two _)

theorem targetDoubled {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (f : Frame (Relations.color (closure G)))
    (g : Frame (targetName p)) (hl : g.l = f.l) (hr : g.r = f.r) (v : Nat)
    (a : Doubled _ f v) : Nonempty (Doubled _ g v) := by
  classical
  obtain ⟨r,_,names⟩ := SmallShore.realize_at p (by decide : 0 < 12) (by decide)
    f.right g.right f.r f.right.injective g.right.injective f.right_iff
    (fun z => by rw [←hr]; exact g.right_iff z) 0 0
  obtain ⟨b,cells,gram⟩ := transport_columns p f g hl r names a.column a.cells
  have full : Function.Surjective a.column := by
    intro e
    have pos := Finset.card_pos.mp (show 0 < (Finset.univ.filter (fun j => a.column j=e)).card by rw [a.twice]; decide)
    obtain ⟨j,hj⟩ := pos
    exact ⟨j,(Finset.mem_filter.mp hj).2⟩
  have two := transfer_twice _ b full a.twice (fun i j => by rw [←edge_overlap,←edge_overlap,gram])
  refine ⟨⟨fun j => b (r.symm j),fun j => by simpa using cells (r.symm j),?_⟩⟩
  intro e
  have eq := Equiv.sum_comp r.symm (fun j => if b j=e then 1 else (0:Nat))
  simpa only [Finset.sum_boole] using eq.trans (by simpa [mult] using two e)

end QGI.Coherent.FourTwelveTypes

