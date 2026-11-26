import FourTwelveTypes

noncomputable section
namespace QGI.Coherent.FourTwelveDispatch
open FourTwelveTypes FourTwelveCycle FourTwelveCycleGraph StrategyColorLaws

abbrev Col (G : Graph 16) := Relations.color (closure G)
abbrev SFrame (G : Graph 16) := Frame (Col G)

def localRow {G : Graph 16} (f : SFrame G) (v : Nat) (j : R) := Finset.univ.filter fun i => crosses f j i = v

private theorem allNeighborhood {G : Graph 16} (f : SFrame G) (j₀ : R) (i₀ : L) (j : R) :
    neighbors (Col G) (crosses f j₀ i₀) (f.right j) = (localRow f (crosses f j₀ i₀) j).map f.left := by
  ext z
  constructor
  · intro hz
    have he := (Finset.mem_filter.mp hz).2
    obtain ⟨i,rfl⟩ := (f.left_iff z).mpr (((Relations.end_colors (closure G) he).2).trans (f.leftDiag i₀))
    exact Finset.mem_map.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,rfl⟩
  · intro hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩

private theorem frame_cards {G : Graph 16} (f : SFrame G) (j : R) (i : L) :
    (fiber G (f.right j)).card = 12 ∧ (fiber G (f.left i)).card = 4 := by
  have left : fiber G (f.left i) = Finset.univ.map f.left := by
    ext z
    simp only [FourTwelveFunctional.fiber_eq,FourTwelveFunctional.source,Finset.mem_map,Finset.mem_univ,true_and]
    rw [show Relations.color (closure G) (f.left i) (f.left i) = f.l from f.leftDiag i]
    exact (f.left_iff z).symm
  have right : fiber G (f.right j) = Finset.univ.map f.right := by
    ext z
    simp only [FourTwelveFunctional.fiber_eq,FourTwelveFunctional.source,Finset.mem_map,Finset.mem_univ,true_and]
    rw [show Relations.color (closure G) (f.right j) (f.right j) = f.r from f.rightDiag j]
    exact (f.right_iff z).symm
  simp [left,right]

/-- A two-colored cross rectangle in which the first color has a two-point
neighborhood at each of the twelve vertices. -/
structure Binary (G : Graph 16) (f : SFrame G) where
  v : Nat
  w : Nat
  different : v ≠ w
  color : ∀ j i, crosses f j i = v ∨ crosses f j i = w
  column : R → Edge
  cols : ∀ j, edge (column j) = localRow f v j
  cells : ∀ j, neighbors (Col G) v (f.right j) = (edge (column j)).map f.left
  select : Bool → Bool
  adjacency : ∀ j i, G.edge (f.right j) (f.left i) = select (decide (crosses f j i = v))

theorem uniform_functional_or_binary {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (q : QuantumIso G H) (f : SFrame G) :
    Isomorphic G H ∨ Nonempty (Binary G f) := by
  classical
  let v := crosses f 0 0
  by_cases uniform : ∀ j i, crosses f j i = v
  · apply Or.inl (twins_graph p f ?_)
    constructor <;> intros <;> simp [uniform]
  push_neg at uniform
  obtain ⟨base,pt,diff⟩ := uniform
  let w := crosses f base pt
  have vw : v ≠ w := Ne.symm diff
  have reg (t : Nat) := (regular (SixTenCoordinates.sourceLaws (closure G)) f t).1
  have constant (t : Nat) (j : R) : (localRow f t j).card = (localRow f t 0).card := by
    simpa [localRow,active,FiberRectangles.degree] using reg t j
  have lo (j : R) (i : L) : 0 < (localRow f (crosses f j i) 0).card :=
    (Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩ :
      0 < (localRow f (crosses f j i) j).card).trans_eq (constant _ _)
  have discharge (j : R) (i : L) (one : (localRow f (crosses f j i) 0).card = 1) : Isomorphic G H := by
    have card := (constant (crosses f j i) j).trans one
    obtain ⟨u,hu⟩ := Finset.card_eq_one.mp card
    have same : u=i := by
      have h : i ∈ localRow f (crosses f j i) j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
      exact (show i=u by simpa [hu] using h).symm
    obtain ⟨twelve,four⟩ := frame_cards f j i
    apply FourTwelveFunctional.isomorphic_of_column_one _ _ twelve four _ q
    intro z hz
    have mem : z ∈ neighbors (Col G) (crosses f j i) (f.right j) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩
    rw [allNeighborhood,hu,same] at mem
    simpa using mem
  by_cases oneV : (localRow f v 0).card = 1
  · exact Or.inl (discharge 0 0 oneV)
  by_cases oneW : (localRow f w 0).card = 1
  · exact Or.inl (discharge base pt oneW)
  have disjoint (j : R) : Disjoint (localRow f v j) (localRow f w j) :=
    Finset.disjoint_left.mpr fun i hv hw => vw (((Finset.mem_filter.mp hv).2).symm.trans (Finset.mem_filter.mp hw).2)
  have bound := Finset.card_le_univ (localRow f v 0 ∪ localRow f w 0)
  rw [Finset.card_union_of_disjoint (disjoint _)] at bound
  change _ ≤ 4 at bound
  have pv : 0 < (localRow f v 0).card := lo 0 0
  have pw : 0 < (localRow f w 0).card := lo base pt
  have two : (localRow f v 0).card = 2 ∧ (localRow f w 0).card = 2 := by omega
  have palette (j : R) (i : L) : crosses f j i = v ∨ crosses f j i = w := by
    have eq : localRow f v j ∪ localRow f w j = Finset.univ := Finset.eq_univ_of_card _ (by
      rw [Finset.card_union_of_disjoint (disjoint _),constant,constant w,two.1,two.2]; decide)
    have h : i ∈ localRow f v j ∪ localRow f w j := eq ▸ Finset.mem_univ _
    simpa only [Finset.mem_union,localRow,Finset.mem_filter,Finset.mem_univ,true_and] using h
  have repr : ∀ s : Finset L, s.card = 2 → ∃ e, edge e = s := by native_decide
  choose a ha using fun j => repr (localRow f v j) ((constant v j).trans two.1)
  let selector := fun t : Bool => if t then G.edge (f.right 0) (f.left 0) else G.edge (f.right base) (f.left pt)
  refine Or.inr ⟨⟨v,w,vw,palette,a,ha,fun j => (allNeighborhood f 0 0 j).trans (congrArg (Finset.map f.left) (ha j).symm),selector,?_⟩⟩
  intro j i
  have law := SixTenCoordinates.Block.edges_self G (rightShore f) (leftShore f)
  rcases palette j i with hit|miss
  · simpa only [selector,hit,decide_true,if_true] using (law hit)
  · have off : crosses f j i ≠ v := fun eq => vw (eq.symm.trans miss)
    simpa only [selector,off,decide_false,if_false] using (law miss)

end QGI.Coherent.FourTwelveDispatch


namespace QGI.Coherent.FourTwelveDispatch
open FourTwelveTypes FourTwelveCycle FourTwelveCycleGraph StrategyColorLaws

variable {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

private def relabelLeft {c : C} (f : Frame c) (p : Equiv.Perm L) : Frame c :=
  ⟨(Equiv.sumCongr p (Equiv.refl R)).trans f.points,f.l,f.r,f.ne,
    fun i => f.leftDiag (p i),f.rightDiag⟩

private theorem degree_info {f : SFrame G} (B : Binary G f) :
    (∀ i, degree B.column i = degree B.column 0) ∧
    ∀ j, mult B.column (B.column j) = mult B.column (B.column 0) := by
  have info := regular (SixTenCoordinates.sourceLaws (closure G)) f B.v
  have membership (j : R) (i : L) : i ∈ edge (B.column j) ↔ crosses f j i = B.v := by
    simp [B.cols,localRow]
  have degrees (i : L) : degree B.column i = FiberRectangles.degree (fun j => active f B.v j i) := by
    simp [degree,FiberRectangles.degree,active,membership]
  have overlap_eq (j y : R) : SixTenCoordinates.Block.overlap (active f B.v) j y = overlap (B.column j) (B.column y) := by
    apply congrArg Finset.card
    ext i
    simp [SixTenCoordinates.Block.overlap,overlap,active,membership]
  have freq (j : R) : SixTenCoordinates.Block.hist (SixTenCoordinates.Block.overlap (active f B.v)) j 2 =
      mult B.column (B.column j) := by
    unfold SixTenCoordinates.Block.hist mult
    apply congrArg Finset.card
    ext y
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,overlap_eq]
    exact (edge_overlap _ _).trans eq_comm
  exact ⟨fun i => (degrees i).trans ((info.2.1 i).trans (degrees 0).symm),
    fun j => (freq j).symm.trans ((info.2.2 j 2).trans (freq 0))⟩

include p in
private theorem of_match {f : SFrame G} (B : Binary G f) (e : Edge)
    (shape : ∀ j, B.column j = e ∨ B.column j = opposite e) : Isomorphic G H := by
  let a := fun j => decide (B.column j = e)
  let b := fun i => decide (i ∈ edge e)
  have ne : opposite e ≠ e := by
    have h : ∀ i, opposite i ≠ i := by native_decide
    exact h e
  have pattern : crosses f = fun j i => if a j = b i then B.v else B.w := by
    funext j i
    have mem : crosses f j i = B.v ↔ i ∈ edge (B.column j) := by simp [B.cols,localRow]
    have agree : crosses f j i = B.v ↔ a j = b i := by
      rcases shape j with h|h
      · simp [mem,h,a,b]
      · simp [mem,h,ne,a,b,opposite_edge]
    by_cases h : crosses f j i = B.v
    · rw [if_pos (agree.mp h),h]
    · rw [if_neg (mt agree.mpr h)]
      exact (B.color j i).resolve_left h
  apply twins_graph p f
  rw [pattern]
  exact SplitRectangle.twins_of_halves _ _ _ _

private theorem of_cycle {f : SFrame G} (B : Binary G f) (perm : Equiv.Perm L)
    (only : ∀ j, ∃ i, edge (B.column j) = (edge (cycle i)).map perm.toEmbedding)
    (full : ∀ i, ∃ j, edge (B.column j) = (edge (cycle i)).map perm.toEmbedding) :
    Nonempty (Presentation G) := by
  choose idx hi using only
  let g := relabelLeft f perm
  refine ⟨⟨g,B.v,fun j => cycle (idx j),fun j => ⟨idx j,rfl⟩,?_,?_,B.select,?_⟩⟩
  · intro i
    obtain ⟨j,hj⟩ := full i
    exact ⟨j,edge_inj ((Finset.map_injective perm.toEmbedding) ((hi j).symm.trans hj))⟩
  · intro j
    change neighbors (Col G) B.v (f.right j) = _
    rw [B.cells,hi,Finset.map_map]
    rfl
  · exact fun j i => B.adjacency j (perm i)

private theorem doubled {f : SFrame G} (B : Binary G f) (full : Function.Surjective B.column)
    (freq : ∀ j, mult B.column (B.column j) = mult B.column (B.column 0)) : Nonempty (Doubled _ f B.v) := by
  have eq (e : Edge) : mult B.column e = mult B.column (B.column 0) := by
    obtain ⟨j,rfl⟩ := full e
    exact freq j
  have sum : ∑ e, mult B.column e = 12 := by
    simpa [mult] using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset R) (Finset.univ : Finset Edge) B.column
  simp only [eq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at sum
  refine ⟨⟨B.column,B.cells,fun e => (eq e).trans ?_⟩⟩
  omega

/-- Exhaust all source cross-rectangle forms from the two fiber cardinalities.
Only the doubled six-edge model still needs its operator realization. -/
theorem reduce_to_doubled (four : ∃ x, (fiber G x).card = 4) (twelve : ∃ x, (fiber G x).card = 12)
    (q : QuantumIso G H)
    (last : ∀ (f : SFrame G) (g : Frame (targetName p)), g.l = f.l → g.r = f.r →
      ∀ v, Doubled _ f v → Doubled _ g v → Isomorphic G H) : Isomorphic G H := by
  obtain ⟨f⟩ := coordinates four twelve
  by_cases doneAlready : Isomorphic G H
  · exact doneAlready
  obtain ⟨B⟩ := (uniform_functional_or_binary p q f).resolve_left doneAlready
  obtain ⟨rows,freq⟩ := degree_info B
  rcases shapes B.column rows with ⟨e,hm⟩|⟨perm,only,full⟩|full
  · exact of_match p B e hm
  · obtain ⟨S⟩ := of_cycle B perm only full
    exact FourTwelveCycleGraph.isomorphic p S
  · obtain ⟨D⟩ := doubled B full freq
    obtain ⟨g,hl,hr⟩ := targetFrame p f
    obtain ⟨T⟩ := targetDoubled p f g hl hr B.v D
    exact last f g hl hr B.v D T

end QGI.Coherent.FourTwelveDispatch

