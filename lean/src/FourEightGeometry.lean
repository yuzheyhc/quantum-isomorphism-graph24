import FourTwelveTypes
import SmallUnionRealization

noncomputable section
namespace QGI.Coherent.FourEightGeometry
open SixTenCoordinates FourTwelveCycle FourTwelveTypes

abbrev L := Fin 4
abbrev Eight := Fin 8

/-- The four-cycle with every edge represented by two of the eight columns.
Its point and column coordinates can both be arbitrary. -/
structure RepeatedCycle (b : Eight → Edge) where
  points : Equiv.Perm L
  label : Eight → Fin 4
  edges : ∀ j, edge (b j) = (edge (cycle (label j))).map points.toEmbedding
  twice : ∀ i, (Finset.univ.filter (fun j => label j=i)).card = 2

private def phase (i : Fin 4) : Bool := decide (i.val%2=0)

/-- On the eight-point shore the Gram test "the two columns have other
than one common neighbor" divides the vertices into two four-point sets. -/
theorem RepeatedCycle.halves {b : Eight → Edge} (C : RepeatedCycle b) :
    ∃ side : Eight → Bool,
      (∀ j k, side j = side k ↔ overlap (b j) (b k) ≠ 1) ∧
      ∀ t, (Finset.univ.filter fun j => side j=t).card = 4 := by
  have shape : ∀ i j : Fin 4, phase i=phase j ↔ overlap (cycle i) (cycle j)≠1 := by native_decide
  have size : ∀ t : Bool, (Finset.univ.filter fun i : Fin 4 => phase i=t).card=2 := by decide
  refine ⟨fun j => phase (C.label j),fun j k => ?_,fun t => ?_⟩
  · simpa only [overlap,C.edges,←Finset.map_inter,Finset.card_map] using shape (C.label j) (C.label k)
  · have sum := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset Eight)
      (Finset.univ.filter (fun i : Fin 4 => phase i=t)) C.label
    simpa [C.twice,size] using sum.symm

private theorem same_multiplicity {b : Eight → Edge} (uniform : ∀ j x, mult b (b j)=mult b (b x)) :
    (Finset.univ.image b).card * mult b (b 0) = 8 := by
  classical
  let s := Finset.univ.image b
  have val (e : Edge) : mult b e = if e∈s then mult b (b 0) else 0 := by
    by_cases h : e∈s
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
      rw [if_pos h]; exact uniform j 0
    · have ne (j : Eight) : b j ≠ e := fun eq => h (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,eq⟩)
      simp [h,mult,ne]
  have total : (∑ e, mult b e) = 8 := by
    simpa [mult] using (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset Eight) (Finset.univ : Finset Edge) b)
  have sum : (∑ e, mult b e) = s.card * mult b (b 0) := calc
    _ = ∑ e : Edge, if e∈s then mult b (b 0) else 0 := Finset.sum_congr rfl (fun e _ => val e)
    _ = _ := by simp
  exact sum.symm.trans total

theorem normalize (b : Eight → Edge) (regular : ∀ i, degree b i = degree b 0)
    (uniform : ∀ j x, mult b (b j)=mult b (b x)) :
    (∃ e, ∀ j, b j=e ∨ b j=opposite e) ∨ Nonempty (RepeatedCycle b) := by
  classical
  let s := Finset.univ.image b
  let μ := mult b (b 0)
  have count : s.card*μ=8 := same_multiplicity uniform
  have bound : s.card ≤ 6 := Finset.card_le_univ _
  rcases shapes b regular with split | ⟨p,contained,covers⟩ | full
  · exact Or.inl split
  · choose label cells using contained
    choose rep hreps using covers
    have cycleInj : Function.Injective (fun i : Fin 4 => edge (cycle i)) := by native_decide
    let embed (i : Fin 4) : {e // e∈s} := ⟨b (rep i),Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩⟩
    have inj : Function.Injective embed := by
      intro i j same
      have h : b (rep i) = b (rep j) := congrArg Subtype.val same
      exact cycleInj (Finset.map_injective _ ((hreps i).symm.trans ((congrArg edge h).trans (hreps j))))
    have lower : 4 ≤ s.card := by simpa using Fintype.card_le_of_injective embed inj
    have mu : μ=2 := by
      obtain h|h|h : s.card=4 ∨ s.card=5 ∨ s.card=6 := by omega
      all_goals rw [h] at count; omega
    refine Or.inr ⟨⟨p,label,cells,fun i => ?_⟩⟩
    have eq (j : Eight) : label j=i ↔ b j=b (rep i) := by
      constructor
      · intro h
        apply edge_inj
        exact (cells j).trans (h ▸ (hreps i).symm)
      · intro h
        exact cycleInj (Finset.map_injective _ ((cells j).symm.trans ((congrArg edge h).trans (hreps i))))
    simpa only [eq,mult] using (uniform (rep i) 0).trans mu
  · have all : s = Finset.univ := Finset.eq_univ_iff_forall.mpr (fun i => by
      obtain ⟨j,hj⟩ := full i; exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩)
    have six : s.card = 6 := by rw [all]; decide
    rw [six] at count
    omega

/-- Applied to the actual colors on a 4-by-8 interface, every basic relation
with two neighbors per column is a repeated matching or a doubled four-cycle. -/
theorem classify {n} {c : Fin n → Fin n → Nat} (law : Laws c c) {l r : Nat}
    (F : Shore c l L) (Y : Shore c r Eight) (v : Nat)
    (two : ∀ j, (Finset.univ.filter fun i => c (atPoint F i) (atPoint Y j)=v).card=2) :
    ∃ b : Eight → Edge, (∀ i j, c (atPoint F i) (atPoint Y j)=v ↔ i∈edge (b j)) ∧
      ((∃ e, ∀ j, b j=e ∨ b j=opposite e) ∨ Nonempty (RepeatedCycle b)) := by
  classical
  let B := fun i j => decide (c (atPoint F i) (atPoint Y j)=v)
  have named : Block F F Y Y B B := fun ⦃_ _ _ _⦄ h => congrArg (fun t => decide (t=v)) h
  have repr : ∀ s : Finset L, s.card=2 → ∃ e, edge e=s := by native_decide
  choose b hb using fun j => repr _ (two j)
  have cells (i j) : (c (atPoint F i) (atPoint Y j)=v) ↔ i∈edge (b j) := by simp [hb]
  have bits (i j) : B i j = true ↔ i∈edge (b j) := by simp [B,cells]
  have rows (i : L) : degree b i=degree b 0 := by
    simpa only [degree,bits] using Block.degree_eq law named i 0
  have same (j k : Eight) : Block.overlap (fun j i => B i j) j k = 2 ↔ b j=b k := by
    have sets : Finset.univ.filter (fun i => B i j=true ∧ B i k=true) = edge (b j) ∩ edge (b k) := by
      ext i; simp [bits]
    simpa only [Block.overlap,sets,overlap] using edge_overlap (b j) (b k)
  have uniform (j x : Eight) : mult b (b j)=mult b (b x) := by
    have h := Block.hist_eq law (Block.gram law (Block.flip law named)) j x 2
    simpa only [Block.hist,same,mult,eq_comm] using h
  exact ⟨b,cells,normalize b rows uniform⟩

theorem gram_color {n} {c : Fin n → Fin n → Nat} (law : Laws c c) {l r : Nat}
    (F : Shore c l L) (Y : Shore c r Eight) (v : Nat) (b : Eight → Edge)
    (cells : ∀ i j, c (atPoint F i) (atPoint Y j)=v ↔ i∈edge (b j)) :
    Block Y Y Y Y (fun i j => overlap (b i) (b j)) (fun i j => overlap (b i) (b j)) := by
  let B := fun i j => decide (c (atPoint F i) (atPoint Y j)=v)
  have named : Block F F Y Y B B := fun ⦃_ _ _ _⦄ h => congrArg (fun t => decide (t=v)) h
  have val (j k : Eight) : Block.overlap (fun j i => B i j) j k = overlap (b j) (b k) := by
    apply congrArg Finset.card
    ext i; simp [B,cells]
  intro i j x y h
  have eq := Block.gram law (Block.flip law named) h
  simpa only [val] using eq

/-- The resulting four-plus-four split on the eight-point shore is a
union of its old basis relations. -/
theorem coherent_halves {n} {c : Fin n → Fin n → Nat} (law : Laws c c) {l r : Nat}
    (F : Shore c l L) (Y : Shore c r Eight) (v : Nat) (b : Eight → Edge)
    (cells : ∀ i j, c (atPoint F i) (atPoint Y j)=v ↔ i∈edge (b j)) (C : RepeatedCycle b) :
    ∃ side : Eight → Bool, (∀ t, (Finset.univ.filter fun j => side j=t).card=4) ∧
      ∀ i j x y, c (atPoint Y i) (atPoint Y j)=c (atPoint Y x) (atPoint Y y) →
        (side i=side j ↔ side x=side y) := by
  obtain ⟨s,hs,size⟩ := C.halves
  refine ⟨s,size,fun i j x y h => ?_⟩
  have eq : overlap (b i) (b j)=overlap (b x) (b y) := gram_color law F Y v b cells h
  rw [hs,hs,eq]

/-- The classification on the two named fibers, independently of the ambient order. -/
theorem interface {n} {G : Graph n} {l r : Nat}
    (F : Shore (Relations.color (closure G)) l L) (Y : Shore (Relations.color (closure G)) r Eight) :
    let c := Relations.color (closure G)
    let M := fun i j => c (atPoint F i) (atPoint Y j)
    (∃ i j, ∀ z, c (atPoint Y j) z=c (atPoint Y j) (atPoint F i) → z=atPoint F i) ∨ SplitRectangle.Twins M ∨
      ∃ v w, (∀ i j, M i j=v ∨ M i j=w) ∧ ∃ b : Eight → Edge,
        (∀ i j, M i j=v ↔ i∈edge (b j)) ∧ Nonempty (RepeatedCycle b) := by
  classical
  let c := Relations.color (closure G)
  let M := fun i j => c (atPoint F i) (atPoint Y j)
  let S (t : Nat) (j : Eight) := Finset.univ.filter (fun i => M i j=t)
  let v := M 0 0
  by_cases all : ∀ i j, M i j=v
  · exact Or.inr (Or.inl ⟨fun i x _ _ y => (all i y).trans (all x y).symm,
      fun _ _ _ _ x => (all x _).trans (all x _).symm⟩)
  push_neg at all
  obtain ⟨i₁,j₁,diff⟩ := all
  let w := M i₁ j₁
  have vw : v ≠ w := Ne.symm diff
  have constant (t : Nat) (j : Eight) : (S t j).card = (S t 0).card := by
    let B := fun i j => decide (M i j=t)
    have name : Block F F Y Y B B := fun ⦃_ _ _ _⦄ h => congrArg (fun u => decide (u=t)) h
    simpa only [S,B,decide_eq_true_eq] using Block.degree_eq (sourceLaws _) (Block.flip (sourceLaws _) name) j 0
  have present (i : L) (j : Eight) : 0 < (S (M i j) 0).card :=
    (Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩ :
      0 < (S (M i j) j).card).trans_eq (constant _ _)
  have singleton (i : L) (j : Eight) (one : (S (M i j) 0).card=1) :
      ∀ z, c (atPoint Y j) z=c (atPoint Y j) (atPoint F i) → z=atPoint F i := by
    intro z hz
    have endz := (Relations.end_colors (closure G) hz).2.trans (F i).property
    let k := F.symm ⟨z,endz⟩
    have loc : atPoint F k=z := congrArg Subtype.val (F.apply_symm_apply _)
    obtain ⟨t,ht⟩ := Finset.card_eq_one.mp ((constant _ j).trans one)
    have kMem : k∈S (M i j) j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      change c (atPoint F k) (atPoint Y j)=_; rw [loc]; exact Relations.transpose _ hz⟩
    have iMem : i∈S (M i j) j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
    rw [ht,Finset.mem_singleton] at kMem iMem
    exact loc.symm.trans (congrArg (atPoint F) (kMem.trans iMem.symm))
  by_cases oneV : (S v 0).card=1
  · exact Or.inl ⟨0,0,singleton 0 0 oneV⟩
  by_cases oneW : (S w 0).card=1
  · exact Or.inl ⟨i₁,j₁,singleton i₁ j₁ oneW⟩
  have disj (j) : Disjoint (S v j) (S w j) := Finset.disjoint_left.mpr
    fun _ av aw => vw (((Finset.mem_filter.mp av).2).symm.trans (Finset.mem_filter.mp aw).2)
  have cap := Finset.card_le_univ (S v 0 ∪ S w 0)
  rw [Finset.card_union_of_disjoint (disj _)] at cap
  change _ ≤ 4 at cap
  have pv : 0 < (S v 0).card := present 0 0
  have pw : 0 < (S w 0).card := present i₁ j₁
  have nv : (S v 0).card=2 := by omega
  have nw : (S w 0).card=2 := by omega
  have palette (i j) : M i j=v ∨ M i j=w := by
    have eq : S v j ∪ S w j=Finset.univ := Finset.eq_univ_of_card _ (by
      rw [Finset.card_union_of_disjoint (disj _),constant,constant w,nv,nw]; decide)
    have h : i ∈ S v j ∪ S w j := eq ▸ Finset.mem_univ _
    simpa only [Finset.mem_union,S,Finset.mem_filter,Finset.mem_univ,true_and] using h
  obtain ⟨b,cells,shape⟩ := classify (sourceLaws _) F Y v (fun j => (constant v j).trans nv)
  rcases shape with ⟨e,matching⟩ | cycle'
  · right; left
    let ls (i : L) := decide (i∈edge e)
    let rs (j : Eight) := decide (b j=e)
    have opposite_ne : ∀ t : Edge, opposite t ≠ t := by native_decide
    have mark (i j) : M i j=v ↔ ls i=rs j := by
      rw [cells i j]
      rcases matching j with a|a
      · simp [ls,rs,a]
      · simp [ls,rs,a,opposite_edge,opposite_ne]
    have eq : M = fun i j => if ls i=rs j then v else w := by
      funext i j
      by_cases hv : M i j=v
      · rw [if_pos ((mark i j).mp hv),hv]
      · rw [if_neg (mt (mark i j).mpr hv)]; exact (palette i j).resolve_left hv
    change SplitRectangle.Twins M
    rw [eq]
    exact SplitRectangle.twins_of_halves ls rs v w
  · exact Or.inr (Or.inr ⟨v,w,palette,b,cells,cycle'⟩)

/-- On an actual pair of coherent fibers of sizes four and eight, the
functional case already realizes the entire graph. Apart from a twin
rectangle, the only remaining interface is the doubled four-cycle. -/
theorem dispatch {n} {G H : Graph n} {l r : Nat} (distinct : l≠r)
    (F : Shore (Relations.color (closure G)) l L) (Y : Shore (Relations.color (closure G)) r Eight)
    (q : QuantumIso G H) (lo : 5 ≤ n := by decide) (hi : n ≤ 17 := by decide) :
    let c := Relations.color (closure G)
    let M := fun i j => c (atPoint F i) (atPoint Y j)
    Isomorphic G H ∨ SplitRectangle.Twins M ∨
      ∃ v w, (∀ i j, M i j=v ∨ M i j=w) ∧ ∃ b : Eight → Edge,
        (∀ i j, M i j=v ↔ i∈edge (b j)) ∧ Nonempty (RepeatedCycle b) := by
  classical
  let c := Relations.color (closure G)
  rcases interface F Y with ⟨i,j,thin⟩ | rest
  swap
  · exact Or.inr rest
  left
  have size : (fiber G (atPoint F i)).card=4 := by
    let e := Equiv.subtypeEquivRight (q := fun z => c z z=l) (fun z =>
      (FourTwelveFunctional.fiber_eq (G := G) (atPoint F i) z).trans (by
        change c z z=c (atPoint F i) (atPoint F i) ↔ c z z=l
        have tag : c (atPoint F i) (atPoint F i)=l := (F i).property
        rw [tag]))
    simpa using Fintype.card_congr (e.trans F.symm)
  have outside : atPoint Y j ∉ fiber G (atPoint F i) := fun hz =>
    distinct (((F i).property.symm.trans ((FourTwelveFunctional.fiber_eq _ _).mp hz).symm).trans (Y j).property)
  obtain ⟨K,ng,ip,_,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  obtain ⟨e,he⟩ := SmallUnion.erase_of_column_one p _ _ outside (by omega) (by omega) thin
  exact ⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun x y => StrategyColorLaws.common_edge p (he x y)⟩

end QGI.Coherent.FourEightGeometry
